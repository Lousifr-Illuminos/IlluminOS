#![no_std]
#![no_main]
#![feature(alloc_error_handler)]

extern crate alloc;
use crate::memory::ALLOCATOR;

use alloc::boxed::Box;
use alloc::vec::Vec;
use bootloader::{entry_point, BootInfo};
use core::{alloc::Layout, panic::PanicInfo, ptr};
use x86_64::{
    registers::control::*,
    structures::paging::{Page, PageTableFlags, PhysFrame, Size4KiB},
    PhysAddr, VirtAddr,
};

mod memory;
mod vga_buffer;

entry_point!(kernel_main);
fn kernel_main(boot_info: &'static BootInfo) -> ! {
    println!("Hello from Microlithic Kernel!");

    let phys_mem_offset = VirtAddr::new(boot_info.physical_memory_offset);
    let mut mapper = unsafe { memory::init(phys_mem_offset) };
    let mut frame_allocator =
        unsafe { memory::BootInfoFrameAllocator::init(&boot_info.memory_map) };

    println!("Initializing heap...");
    // Initialize the heap
    match memory::init_heap(&mut mapper, &mut frame_allocator) {
        Ok(_) => println!("Heap initialized successfully."),
        Err(e) => panic!("Failed to initialize heap: {:?}", e),
    }

    println!("Starting allocation tests...");
    {
        // Test the allocator with the smallest allocation
        println!("Attempting smallest allocation...");
        let smallest: Box<u8> = Box::<u8>::new(u8::MAX);
        println!(
            "Maximum value of smallest allocation: {smallest} at address {:p}",
            smallest
        );
    }
    // Try a small allocation
    println!("Attempting small allocation...");
    let small: Box<u16> = Box::<u16>::new(u16::MAX);
    println!(
        "Maximum value of small allocation: {small} at address {:p}",
        small
    );

    // Try a larger allocation
    println!("Attempting larger allocation...");
    let larger: Box<u32> = Box::<u32>::new(u32::MAX);
    println!(
        "Maximum value of larger allocation: {larger} at address {:p}",
        larger
    );

    // Try an even larger allocation
    println!("Attempting even larger allocation...");
    let even_larger: Box<u64> = Box::<u64>::new(u64::MAX);
    println!(
        "Maximum value of even larger allocation: {even_larger} at address {:p}",
        even_larger
    );

    // Try the largest allocation
    println!("Attempting largest allocation...");
    let largest: Box<u128> = Box::<u128>::new(u128::MAX);
    println!(
        "Maximum value of largest allocation: {largest} at address {:p}",
        largest
    );

    // Create a empty vector
    println!("Creating empty vector...");
    let mut empty_vec: Vec<u8> = Vec::new();
    println!("Empty vector created");

    empty_vec.push(32);

    // Create a vector with capacity of 10
    println!("Creating vector with capacity of 10...");
    let mut vec_with_capacity: Vec<u8> = Vec::with_capacity(10);
    println!("Vector with capacity of 10 created");

    vec_with_capacity[0] = 32;

    println!("All allocation tests passed!");

    loop {
        x86_64::instructions::hlt();
    }
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    println!("KERNEL PANIC");
    if let Some(location) = info.location() {
        println!("Location: {}:{}", location.file(), location.line());
    }
    println!("Message: {}", info.message());

    // Attempt to dump heap state
    println!("Attempting to dump heap state...");
    ALLOCATOR.dump_heap();

    loop {
        x86_64::instructions::hlt();
    }
}

#[alloc_error_handler]
fn alloc_error_handler(layout: alloc::alloc::Layout) -> ! {
    panic!("Allocation error: {:?}", layout);
}
