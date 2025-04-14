#![no_std]

#[macro_use]
extern crate alloc;

mod devops_impl;

mod block;

pub use block::Block;
