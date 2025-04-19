// Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Explicit endian types useful for embedding in structs or reinterpreting data.
//!
//! Each endian type is guaarnteed to have the same size and alignment as a regular unsigned
//! primitive of the equal size.
//!
//! # Examples
//!
//! ```
//! # use vm_memory::{Be32, Le32};
//! #
//! let b: Be32 = From::from(3);
//! let l: Le32 = From::from(3);
//!
//! assert_eq!(b.to_native(), 3);
//! assert_eq!(l.to_native(), 3);
//! assert!(b == 3);
//! assert!(l == 3);
//!
//! let b_trans: u32 = unsafe { std::mem::transmute(b) };
//! let l_trans: u32 = unsafe { std::mem::transmute(l) };
//!
//! #[cfg(target_endian = "little")]
//! assert_eq!(l_trans, 3);
//! #[cfg(target_endian = "big")]
//! assert_eq!(b_trans, 3);
//!
//! assert_ne!(b_trans, l_trans);
//! ```

use core::mem::{align_of, size_of};

// use crate::bytes::ByteValued;
use super::bytes::ByteValued;

macro_rules! const_assert {
    ($condition:expr) => {
        let _ = [(); 0 - !$condition as usize];
    };
}

macro_rules! endian_type {
    ($old_type:ident, $new_type:ident, $to_new:ident, $from_new:ident) => {
        /// An unsigned integer type of with an explicit endianness.
        ///
        /// See module level documentation for examples.
        #[derive(Copy, Clone, Eq, PartialEq, Debug, Default)]
        pub struct $new_type($old_type);

        impl $new_type {
            fn _assert() {
                const_assert!(align_of::<$new_type>() == align_of::<$old_type>());
                const_assert!(size_of::<$new_type>() == size_of::<$old_type>());
            }

            /// Converts `self` to the native endianness.
            pub fn to_native(self) -> $old_type {
                $old_type::$from_new(self.0)
            }
        }

        // SAFETY: Safe because we are using this for implementing ByteValued for endian types
        // which are POD.
        unsafe impl ByteValued for $new_type {}

        impl PartialEq<$old_type> for $new_type {
            fn eq(&self, other: &$old_type) -> bool {
                self.0 == $old_type::$to_new(*other)
            }
        }

        impl PartialEq<$new_type> for $old_type {
            fn eq(&self, other: &$new_type) -> bool {
                $old_type::$to_new(other.0) == *self
            }
        }

        impl From<$new_type> for $old_type {
            fn from(v: $new_type) -> $old_type {
                v.to_native()
            }
        }

        impl From<$old_type> for $new_type {
            fn from(v: $old_type) -> $new_type {
                $new_type($old_type::$to_new(v))
            }
        }
    };
}

// 为特定类型实现 endian_type，避免跨大小类型转换
endian_type!(u16, Le16, to_le, from_le);
endian_type!(u32, Le32, to_le, from_le);
endian_type!(u64, Le64, to_le, from_le);
endian_type!(u16, Be16, to_be, from_be);
endian_type!(u32, Be32, to_be, from_be);
endian_type!(u64, Be64, to_be, from_be);

// 为 usize 类型单独实现，避免与其他类型之间的互相转换
#[derive(Copy, Clone, Eq, PartialEq, Debug, Default)]
pub struct LeSize(usize);

impl LeSize {
    /// Converts `self` to the native endianness.
    pub fn to_native(self) -> usize {
        usize::from_le(self.0)
    }
}

// SAFETY: Safe because we are using this for implementing ByteValued for endian types
// which are POD.
unsafe impl ByteValued for LeSize {}

impl PartialEq<usize> for LeSize {
    fn eq(&self, other: &usize) -> bool {
        self.0 == usize::to_le(*other)
    }
}

impl PartialEq<LeSize> for usize {
    fn eq(&self, other: &LeSize) -> bool {
        usize::to_le(other.0) == *self
    }
}

impl From<LeSize> for usize {
    fn from(v: LeSize) -> usize {
        v.to_native()
    }
}

impl From<usize> for LeSize {
    fn from(v: usize) -> LeSize {
        LeSize(usize::to_le(v))
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Default)]
pub struct BeSize(usize);

impl BeSize {
    /// Converts `self` to the native endianness.
    pub fn to_native(self) -> usize {
        usize::from_be(self.0)
    }
}

// SAFETY: Safe because we are using this for implementing ByteValued for endian types
// which are POD.
unsafe impl ByteValued for BeSize {}

impl PartialEq<usize> for BeSize {
    fn eq(&self, other: &usize) -> bool {
        self.0 == usize::to_be(*other)
    }
}

impl PartialEq<BeSize> for usize {
    fn eq(&self, other: &BeSize) -> bool {
        usize::to_be(other.0) == *self
    }
}

impl From<BeSize> for usize {
    fn from(v: BeSize) -> usize {
        v.to_native()
    }
}

impl From<usize> for BeSize {
    fn from(v: usize) -> BeSize {
        BeSize(usize::to_be(v))
    }
}
