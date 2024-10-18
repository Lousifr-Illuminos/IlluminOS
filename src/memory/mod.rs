use crate::println;

use bootloader::bootinfo::{MemoryMap, MemoryRegionType};
use core::alloc::{GlobalAlloc, Layout};
use core::mem::MaybeUninit;
use core::ptr::{self, NonNull};
use core::sync::atomic::{AtomicPtr, Ordering};
use x86_64::structures::paging::mapper::MapToError;
use x86_64::{
    structures::paging::{
        FrameAllocator, Mapper, OffsetPageTable, Page, PageTableFlags, PhysFrame, Size4KiB,
    },
    PhysAddr, VirtAddr,
};

pub const HEAP_START: usize = 0x_4444_4444_0000;
pub const HEAP_SIZE: usize = 512 * 1024; // 0.5 MiB

const BLOCK_SIZE_MIN: usize = 8;
const BLOCK_SIZE_MAX: usize = 128;
const FIRST_LEVEL_INDEX_COUNT: usize = 32;
const SECOND_LEVEL_INDEX_COUNT: usize = 16;

pub fn init_heap(
    mapper: &mut impl Mapper<Size4KiB>,
    frame_allocator: &mut impl FrameAllocator<Size4KiB>,
) -> Result<(), MapToError<Size4KiB>> {
    let page_range = {
        let heap_start = VirtAddr::new(HEAP_START as u64);
        let heap_end = heap_start + HEAP_SIZE - 1u64;
        let heap_start_page = Page::containing_address(heap_start);
        let heap_end_page = Page::containing_address(heap_end);
        Page::range_inclusive(heap_start_page, heap_end_page)
    };

    for page in page_range {
        let frame = frame_allocator
            .allocate_frame()
            .ok_or(MapToError::FrameAllocationFailed)?;
        let flags = PageTableFlags::PRESENT | PageTableFlags::WRITABLE;
        unsafe {
            mapper.map_to(page, frame, flags, frame_allocator)?.flush();
        }
        println!("Mapped page {:?} to frame {:?}", page, frame);
    }

    unsafe {
        ALLOCATOR.init(HEAP_START, HEAP_SIZE);
    }

    Ok(())
}

pub struct BootInfoFrameAllocator {
    memory_map: &'static MemoryMap,
    next: usize,
}

impl BootInfoFrameAllocator {
    pub unsafe fn init(memory_map: &'static MemoryMap) -> Self {
        BootInfoFrameAllocator {
            memory_map,
            next: 0,
        }
    }

    fn usable_frames(&self) -> impl Iterator<Item = PhysFrame> {
        let regions = self.memory_map.iter();
        let usable_regions = regions.filter(|r| r.region_type == MemoryRegionType::Usable);
        let addr_ranges = usable_regions.map(|r| r.range.start_addr()..r.range.end_addr());
        let frame_addresses = addr_ranges.flat_map(|r| r.step_by(4096));
        frame_addresses.map(|addr| PhysFrame::containing_address(PhysAddr::new(addr)))
    }
}

unsafe impl FrameAllocator<Size4KiB> for BootInfoFrameAllocator {
    fn allocate_frame(&mut self) -> Option<PhysFrame> {
        let frame = self.usable_frames().nth(self.next);
        self.next += 1;
        frame
    }
}

pub unsafe fn init(physical_memory_offset: VirtAddr) -> impl Mapper<Size4KiB> {
    let level_4_table = active_level_4_table(physical_memory_offset);
    OffsetPageTable::new(level_4_table, physical_memory_offset)
}

unsafe fn active_level_4_table(
    physical_memory_offset: VirtAddr,
) -> &'static mut x86_64::structures::paging::PageTable {
    use x86_64::registers::control::Cr3;

    let (level_4_table_frame, _) = Cr3::read();

    let phys = level_4_table_frame.start_address();
    let virt = physical_memory_offset + phys.as_u64();
    let page_table_ptr: *mut x86_64::structures::paging::PageTable = virt.as_mut_ptr();

    &mut *page_table_ptr
}

#[derive(Debug)]
#[repr(C, align(8))]
struct Block {
    size: usize,
    is_free: bool,
    next: AtomicPtr<Block>,
}

pub struct TLSF {
    blocks: [[AtomicPtr<Block>; SECOND_LEVEL_INDEX_COUNT]; FIRST_LEVEL_INDEX_COUNT],
}

impl TLSF {
    pub const fn new() -> Self {
        let blocks: [[MaybeUninit<AtomicPtr<Block>>; SECOND_LEVEL_INDEX_COUNT];
            FIRST_LEVEL_INDEX_COUNT] = unsafe { MaybeUninit::uninit().assume_init() };

        let mut blocks = blocks;
        let mut i = 0;
        while i < FIRST_LEVEL_INDEX_COUNT {
            let mut j = 0;
            while j < SECOND_LEVEL_INDEX_COUNT {
                blocks[i][j] = MaybeUninit::new(AtomicPtr::new(core::ptr::null_mut()));
                j += 1;
            }
            i += 1;
        }

        TLSF {
            blocks: unsafe { core::mem::transmute(blocks) },
        }
    }

    pub unsafe fn init(&self, heap_start: usize, heap_size: usize) {
        println!(
            "Initializing heap: start={:x}, size={}",
            heap_start, heap_size
        );
        let aligned_start = (heap_start + BLOCK_SIZE_MIN - 1) & !(BLOCK_SIZE_MIN - 1);
        let aligned_size = heap_size.saturating_sub(aligned_start.saturating_sub(heap_start));
        println!(
            "Aligned heap: start={:x}, size={}",
            aligned_start, aligned_size
        );
        if aligned_size < BLOCK_SIZE_MIN {
            panic!("Heap size too small");
        }
        let block_ptr = aligned_start as *mut Block;
        (*block_ptr).size = aligned_size;
        (*block_ptr).next = AtomicPtr::new(core::ptr::null_mut());
        let (first_level, second_level) = self.get_index_for_size(aligned_size);
        println!(
            "Initial block: size={}, first_level={}, second_level={}",
            aligned_size, first_level, second_level
        );
        self.add_free_block(block_ptr, first_level, second_level);
    }

    pub fn validate_heap(&self) -> Result<(), &'static str> {
        for first_level in 0..FIRST_LEVEL_INDEX_COUNT {
            for second_level in 0..SECOND_LEVEL_INDEX_COUNT {
                let mut block_ptr = self.blocks[first_level][second_level].load(Ordering::Relaxed);
                while !block_ptr.is_null() {
                    let block = unsafe { &*block_ptr };
                    println!(
                        "Validating block at {:p}, size: {}, is_free: {}",
                        block_ptr, block.size, block.is_free
                    );
                    if block.size < BLOCK_SIZE_MIN {
                        return Err("Block size smaller than BLOCK_SIZE_MIN");
                    }
                    if !block.is_free {
                        return Err("Free block marked as allocated");
                    }
                    if (block_ptr as usize) % 8 != 0 {
                        return Err("Block not aligned to 8 bytes");
                    }
                    // Check for overlapping blocks
                    let next_block =
                        unsafe { (block_ptr as *mut u8).add(block.size) as *mut Block };
                    if !next_block.is_null() && next_block <= block_ptr {
                        return Err("Overlapping blocks detected");
                    }
                    block_ptr = block.next.load(Ordering::Relaxed);
                }
            }
        }
        Ok(())
    }

    pub fn dump_heap(&self) {
        println!("Heap dump:");
        for first_level in 0..FIRST_LEVEL_INDEX_COUNT {
            for second_level in 0..SECOND_LEVEL_INDEX_COUNT {
                let mut block_ptr = self.blocks[first_level][second_level].load(Ordering::Relaxed);
                if !block_ptr.is_null() {
                    println!("Level [{},{}]:", first_level, second_level);
                    while !block_ptr.is_null() {
                        let block = unsafe { &*block_ptr };
                        println!("  Block at {:p}, size: {}", block_ptr, block.size);
                        block_ptr = block.next.load(Ordering::Relaxed);
                    }
                }
            }
        }
    }

    fn alloc(&self, layout: Layout) -> *mut u8 {
        let size = layout.size().max(layout.align()).max(BLOCK_SIZE_MIN);
        let align = layout.align().max(8);

        let size = (size + align - 1) & !(align - 1);

        let (first_level, second_level) = self.get_suitable_block(size);

        if let Some(block_ptr) = self.find_free_block(first_level, second_level) {
            let block = unsafe { &mut *block_ptr.as_ptr() };

            self.remove_free_block(block_ptr, first_level, second_level);

            let block_start = block_ptr.as_ptr() as usize;
            let aligned_start = (block_start + align - 1) & !(align - 1);
            let alignment_offset = aligned_start - block_start;

            if block.size >= size + alignment_offset {
                if alignment_offset > 0 {
                    let padding_block = block_ptr.as_ptr();
                    unsafe {
                        (*padding_block).size = alignment_offset;
                        (*padding_block).next = AtomicPtr::new(ptr::null_mut());
                    }
                    let (padding_first_level, padding_second_level) =
                        self.get_index_for_size(alignment_offset);
                    self.add_free_block(padding_block, padding_first_level, padding_second_level);
                }

                let aligned_block = aligned_start as *mut Block;
                unsafe {
                    (*aligned_block).size = block.size - alignment_offset;
                    (*aligned_block).is_free = false; // Mark as not free

                    if (*aligned_block).size > size {
                        self.split_block(aligned_block, size);
                    }
                }

                let result_ptr = aligned_block as *mut u8;

                debug_assert!(
                    result_ptr as usize % align == 0,
                    "Misaligned allocation: {:p} with align {}",
                    result_ptr,
                    align
                );

                result_ptr
            } else {
                ptr::null_mut()
            }
        } else {
            ptr::null_mut()
        }
    }

    fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if ptr.is_null() {
            return;
        }

        let block_ptr = (ptr as usize & !(BLOCK_SIZE_MIN - 1)) as *mut Block;
        let block = unsafe { &mut *block_ptr };

        // Mark the block as free
        block.is_free = true;

        // Merge with adjacent blocks
        self.merge_block(block_ptr);

        let (first_level, second_level) = self.get_index_for_size(block.size);
        self.add_free_block(block_ptr, first_level, second_level);

        // New error handling
        if let Err(e) = self.validate_heap() {
            panic!("Heap validation failed after deallocation: {}", e);
        }
    }

    fn get_suitable_block(&self, size: usize) -> (usize, usize) {
        let size = size.max(BLOCK_SIZE_MIN);
        let mut first_level =
            (size.ilog2() as usize).saturating_sub(BLOCK_SIZE_MIN.ilog2() as usize);
        if first_level >= FIRST_LEVEL_INDEX_COUNT {
            first_level = FIRST_LEVEL_INDEX_COUNT - 1;
        }
        let second_level = ((size >> first_level) - 1) & (SECOND_LEVEL_INDEX_COUNT - 1);
        (first_level, second_level)
    }

    fn find_free_block(
        &self,
        mut first_level: usize,
        mut second_level: usize,
    ) -> Option<NonNull<Block>> {
        while first_level < FIRST_LEVEL_INDEX_COUNT {
            for level in second_level..SECOND_LEVEL_INDEX_COUNT {
                let block_ptr = self.blocks[first_level][level].load(Ordering::Acquire);
                if !block_ptr.is_null() {
                    let block = unsafe { &*block_ptr };
                    if block.size >= BLOCK_SIZE_MIN {
                        return NonNull::new(block_ptr);
                    }
                }
            }
            first_level += 1;
            second_level = 0;
        }
        None
    }

    fn get_previous_block(&self, block_ptr: *mut Block) -> Option<*mut Block> {
        let heap_start = HEAP_START as *mut Block;
        let heap_end = unsafe { heap_start.add(HEAP_SIZE / core::mem::size_of::<Block>()) };

        // Check if the block_ptr is within the heap bounds and properly aligned
        if block_ptr < heap_start || block_ptr >= heap_end || (block_ptr as usize) % 8 != 0 {
            println!("Block pointer is out of heap bounds or misaligned");
            return None;
        }

        // If it's the first block, there's no previous block
        if block_ptr == heap_start {
            println!("Block is the first block in the heap");
            return None;
        }

        let mut current = heap_start;

        while current < block_ptr {
            let current_size = unsafe { (*current).size };
            println!("Current block: {:p}, size: {}", current, current_size);

            // Ensure the current size is at least the minimum block size
            if current_size < BLOCK_SIZE_MIN {
                println!("Error: Invalid block size");
                return None;
            }

            let next = unsafe { (current as *mut u8).add(current_size) as *mut Block };

            // Ensure the next block is properly aligned
            if (next as usize) % 8 != 0 {
                println!("Error: Next block is misaligned");
                return None;
            }

            // If the next block would be our target block, we've found the previous
            if next == block_ptr {
                println!("Found previous block: {:p}", current);
                return Some(current);
            }

            // If we've gone past our target block, something is wrong
            if next > block_ptr {
                println!("Error: Went past target block");
                return None;
            }

            current = next;
        }

        // If we've reached here, we didn't find a previous block
        println!("No previous block found");
        None
    }

    fn add_free_block(&self, block: *mut Block, first_level: usize, second_level: usize) {
        let block_ref = unsafe { &mut *block };
        if block_ref.size < BLOCK_SIZE_MIN {
            println!("Error: Attempting to add a block smaller than BLOCK_SIZE_MIN");
            return;
        }
        block_ref.is_free = true;
        let current_head = self.blocks[first_level][second_level].load(Ordering::Relaxed);
        block_ref.next.store(current_head, Ordering::Relaxed);
        self.blocks[first_level][second_level].store(block, Ordering::Release);
    }

    fn remove_free_block(&self, block: NonNull<Block>, first_level: usize, second_level: usize) {
        let block_ref = unsafe { block.as_ref() };
        let next_ptr = block_ref.next.load(Ordering::Relaxed);
        self.blocks[first_level][second_level].store(next_ptr, Ordering::Release);
    }

    fn split_block(&self, block_ptr: *mut Block, size: usize) {
        unsafe {
            let block = &mut *block_ptr;
            let remaining_size = block.size - size;
            if remaining_size >= BLOCK_SIZE_MIN {
                let new_block_ptr = (block_ptr as *mut u8).add(size) as *mut Block;
                let new_block = &mut *new_block_ptr;
                new_block.size = remaining_size;
                new_block.next = AtomicPtr::new(ptr::null_mut());
                new_block.is_free = true; // Mark the new block as free

                block.size = size;
                block.is_free = false; // Mark the allocated block as not free

                let (first_level, second_level) = self.get_index_for_size(remaining_size);
                self.add_free_block(new_block_ptr, first_level, second_level);
            } else {
                block.is_free = false; // Mark the entire block as not free if we can't split
            }
        }
    }

    fn merge_block(&self, block_ptr: *mut Block) {
        if block_ptr.is_null() {
            return;
        }

        let mut current_ptr = block_ptr;
        let mut current_block = unsafe { &mut *current_ptr };
        let mut total_size = current_block.size;

        // Check and merge with the previous block
        if let Some(prev_block_ptr) = self.get_previous_block(block_ptr) {
            let prev_block = unsafe { &mut *prev_block_ptr };
            if prev_block.is_free {
                let (prev_first_level, prev_second_level) =
                    self.get_index_for_size(prev_block.size);
                self.remove_free_block(
                    NonNull::new(prev_block_ptr).unwrap(),
                    prev_first_level,
                    prev_second_level,
                );
                total_size += prev_block.size;
                current_ptr = prev_block_ptr;
                current_block = unsafe { &mut *current_ptr };
            }
        }

        // Check and merge with the next block
        let next_block_ptr =
            unsafe { (current_ptr as *mut u8).add(current_block.size) as *mut Block };
        if !next_block_ptr.is_null() {
            let next_block = unsafe { &mut *next_block_ptr };
            if next_block.is_free {
                let (next_first_level, next_second_level) =
                    self.get_index_for_size(next_block.size);
                self.remove_free_block(
                    NonNull::new(next_block_ptr).unwrap(),
                    next_first_level,
                    next_second_level,
                );
                total_size += next_block.size;
            }
        }

        // Update the size of the merged block
        current_block.size = total_size;
        current_block.is_free = true; // Ensure the merged block is marked as free
    }

    fn get_index_for_size(&self, size: usize) -> (usize, usize) {
        if size < BLOCK_SIZE_MIN {
            return (0, 0);
        }
        let first_level = ((size.ilog2() as usize).saturating_sub(BLOCK_SIZE_MIN.ilog2() as usize))
            .min(FIRST_LEVEL_INDEX_COUNT - 1);
        let second_level = ((size >> first_level) - 1) & (SECOND_LEVEL_INDEX_COUNT - 1);
        (first_level, second_level)
    }
}

unsafe impl GlobalAlloc for TLSF {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        self.alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        self.dealloc(ptr, layout)
    }
}

#[global_allocator]
pub static ALLOCATOR: TLSF = TLSF::new();
