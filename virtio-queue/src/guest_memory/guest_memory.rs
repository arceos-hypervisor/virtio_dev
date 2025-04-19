use core::cmp::Ordering;

use super::bytes::{AtomicAccess, Bytes};
use super::memory_io::WriteVolatile;
use super::{bitmap::Bitmap, memory_io::ReadVolatile};
use axaddrspace::{GuestPhysAddr, GuestPhysAddrRange};
use memory_addr::MemoryAddr;
/// Result of guest memory operations.
// pub type Result<T> = std::result::Result<T, Error>;

/// Errors associated with handling guest memory accesses.
#[allow(missing_docs)]
#[derive(Debug)]
pub enum Error {
    /// Failure in finding a guest address in any memory regions mapped by this guest.
    InvalidGuestAddress(GuestPhysAddr),
    /// Couldn't read/write from the given source.
    IOError,
    /// Incomplete read or write.
    PartialBuffer { expected: usize, completed: usize },
    /// Requested backend address is out of range.
    InvalidBackendAddress,
    /// Host virtual address not available.
    HostAddressNotAvailable,
    /// The length returned by the callback passed to `try_access` is outside the address range.
    CallbackOutOfRange,
    /// The address to be read by `try_access` is outside the address range.
    GuestAddressOverflow,
}

pub type Result<T> = core::result::Result<T, Error>;

/// Represents a continuous region of guest physical memory.
#[allow(clippy::len_without_is_empty)]
pub trait GuestMemoryRegion: Bytes<GuestPhysAddrRange, E = Error> {
    /// Type used for dirty memory tracking.
    type B: Bitmap;

    /// Returns the size of the region.
    fn len(&self) -> usize;

    /// Returns the minimum (inclusive) address managed by the region.
    fn start_addr(&self) -> GuestPhysAddr;

    /// Returns the maximum (inclusive) address managed by the region.
    fn last_addr(&self) -> GuestPhysAddr {
        // unchecked_add is safe as the region bounds were checked when it was created.
        self.start_addr().checked_add(self.len() - 1).unwrap()
    }

    /// Borrow the associated `Bitmap` object.
    fn bitmap(&self) -> &Self::B;

    /// Returns the given address if it is within this region.
    fn check_address(&self, addr: GuestPhysAddrRange) -> Option<GuestPhysAddrRange> {
        if self.address_in_range(addr) {
            Some(addr)
        } else {
            None
        }
    }

    /// Returns `true` if the given address is within this region.
    fn address_in_range(&self, addr: GuestPhysAddrRange) -> bool {
        addr.size() < self.len()
    }

    /// Returns the address plus the offset if it is in this region.
    fn checked_offset(
        &self,
        base: GuestPhysAddrRange,
        offset: usize,
    ) -> Option<GuestPhysAddrRange> {
        // base.checked_add(offset as usize)
        //     .and_then(|addr| self.check_address(addr))
        let addr = GuestPhysAddr::from(base.start + offset);
        Some(GuestPhysAddrRange::from_start_size(addr, base.size()))
            .and_then(|addr| self.check_address(addr))
    }

    /// Tries to convert an absolute address to a relative address within this region.
    ///
    /// Returns `None` if `addr` is out of the bounds of this region.
    fn to_region_addr(&self, addr: GuestPhysAddr) -> Option<GuestPhysAddrRange> {
        let offset = addr.sub(self.start_addr().as_usize());
        self.check_address(GuestPhysAddrRange::from_start_size(offset, 1))
    }

    /// Returns the host virtual address corresponding to the region address.
    ///
    /// Some [`GuestMemory`](trait.GuestMemory.html) implementations, like `GuestMemoryMmap`,
    /// have the capability to mmap guest address range into host virtual address space for
    /// direct access, so the corresponding host virtual address may be passed to other subsystems.
    ///
    /// # Note
    /// The underlying guest memory is not protected from memory aliasing, which breaks the
    /// Rust memory safety model. It's the caller's responsibility to ensure that there's no
    /// concurrent accesses to the underlying guest memory.
    fn get_host_address(&self, _addr: GuestPhysAddrRange) -> Result<*mut u8> {
        Err(Error::HostAddressNotAvailable)
    }

    // /// Returns information regarding the file and offset backing this memory region.
    // fn file_offset(&self) -> Option<&FileOffset> {
    //     None
    // }

    /// Returns a slice corresponding to the data in the region.
    ///
    /// Returns `None` if the region does not support slice-based access.
    ///
    /// # Safety
    ///
    /// Unsafe because of possible aliasing.
    #[deprecated = "It is impossible to use this function for accessing memory of a running virtual \
    machine without violating aliasing rules "]
    unsafe fn as_slice(&self) -> Option<&[u8]> {
        None
    }

    /// Returns a mutable slice corresponding to the data in the region.
    ///
    /// Returns `None` if the region does not support slice-based access.
    ///
    /// # Safety
    ///
    /// Unsafe because of possible aliasing. Mutable accesses performed through the
    /// returned slice are not visible to the dirty bitmap tracking functionality of
    /// the region, and must be manually recorded using the associated bitmap object.
    #[deprecated = "It is impossible to use this function for accessing memory of a running virtual \
    machine without violating aliasing rules "]
    unsafe fn as_mut_slice(&self) -> Option<&mut [u8]> {
        None
    }

    // /// Returns a [`VolatileSlice`](struct.VolatileSlice.html) of `count` bytes starting at
    // /// `offset`.
    // #[allow(unused_variables)]
    // fn get_slice(
    //     &self,
    //     offset: GuestPhysAddrRange,
    //     count: usize,
    // ) -> Result<VolatileSlice<BS<Self::B>>> {
    //     Err(Error::HostAddressNotAvailable)
    // }

    // /// Gets a slice of memory for the entire region that supports volatile access.
    // ///
    // /// # Examples (uses the `backend-mmap` feature)
    // ///
    // /// ```
    // /// # #[cfg(feature = "backend-mmap")]
    // /// # {
    // /// # use vm_memory::{GuestAddress, MmapRegion, GuestRegionMmap, GuestMemoryRegion};
    // /// # use vm_memory::volatile_memory::{VolatileMemory, VolatileSlice, VolatileRef};
    // /// #
    // /// let region = GuestRegionMmap::<()>::from_range(GuestAddress(0x0), 0x400, None)
    // ///     .expect("Could not create guest memory");
    // /// let slice = region
    // ///     .as_volatile_slice()
    // ///     .expect("Could not get volatile slice");
    // ///
    // /// let v = 42u32;
    // /// let r = slice
    // ///     .get_ref::<u32>(0x200)
    // ///     .expect("Could not get reference");
    // /// r.store(v);
    // /// assert_eq!(r.load(), v);
    // /// # }
    // /// ```
    // fn as_volatile_slice(&self) -> Result<VolatileSlice<BS<Self::B>>> {
    //     self.get_slice(GuestPhysAddrRange(0), self.len() as usize)
    // }

    /// Show if the region is based on the `HugeTLBFS`.
    /// Returns Some(true) if the region is backed by hugetlbfs.
    /// None represents that no information is available.
    ///
    /// # Examples (uses the `backend-mmap` feature)
    ///
    /// ```
    /// # #[cfg(feature = "backend-mmap")]
    /// # {
    /// #   use vm_memory::{GuestAddress, GuestMemory, GuestMemoryMmap, GuestRegionMmap};
    /// let addr = GuestAddress(0x1000);
    /// let mem = GuestMemoryMmap::<()>::from_ranges(&[(addr, 0x1000)]).unwrap();
    /// let r = mem.find_region(addr).unwrap();
    /// assert_eq!(r.is_hugetlbfs(), None);
    /// # }
    /// ```
    #[cfg(target_os = "linux")]
    fn is_hugetlbfs(&self) -> Option<bool> {
        None
    }
}

/// `GuestMemory` represents a container for an *immutable* collection of
/// `GuestMemoryRegion` objects.  `GuestMemory` provides the `Bytes<GuestAddress>`
/// trait to hide the details of accessing guest memory by physical address.
/// Interior mutability is not allowed for implementations of `GuestMemory` so
/// that they always provide a consistent view of the memory map.
///
/// The task of the `GuestMemory` trait are:
/// - map a request address to a `GuestMemoryRegion` object and relay the request to it.
/// - handle cases where an access request spanning two or more `GuestMemoryRegion` objects.
pub trait GuestMemory {
    /// Type of objects hosted by the address space.
    type R: GuestMemoryRegion;

    /// Returns the number of regions in the collection.
    fn num_regions(&self) -> usize;

    /// Returns the region containing the specified address or `None`.
    fn find_region(&self, addr: GuestPhysAddr) -> Option<&Self::R>;

    /// Perform the specified action on each region.
    ///
    /// It only walks children of current region and does not step into sub regions.
    #[deprecated(since = "0.6.0", note = "Use `.iter()` instead")]
    fn with_regions<F, E>(&self, cb: F) -> core::result::Result<(), E>
    where
        F: Fn(usize, &Self::R) -> core::result::Result<(), E>,
    {
        for (index, region) in self.iter().enumerate() {
            cb(index, region)?;
        }
        Ok(())
    }

    /// Perform the specified action on each region mutably.
    ///
    /// It only walks children of current region and does not step into sub regions.
    #[deprecated(since = "0.6.0", note = "Use `.iter()` instead")]
    fn with_regions_mut<F, E>(&self, mut cb: F) -> core::result::Result<(), E>
    where
        F: FnMut(usize, &Self::R) -> core::result::Result<(), E>,
    {
        for (index, region) in self.iter().enumerate() {
            cb(index, region)?;
        }
        Ok(())
    }

    /// Gets an iterator over the entries in the collection.
    ///
    /// # Examples
    ///
    /// * Compute the total size of all memory mappings in KB by iterating over the memory regions
    ///   and dividing their sizes to 1024, then summing up the values in an accumulator. (uses the
    ///   `backend-mmap` feature)
    ///
    /// ```
    /// # #[cfg(feature = "backend-mmap")]
    /// # {
    /// # use vm_memory::{GuestAddress, GuestMemory, GuestMemoryRegion, GuestMemoryMmap};
    /// #
    /// let start_addr1 = GuestAddress(0x0);
    /// let start_addr2 = GuestAddress(0x400);
    /// let gm = GuestMemoryMmap::<()>::from_ranges(&vec![(start_addr1, 1024), (start_addr2, 2048)])
    ///     .expect("Could not create guest memory");
    ///
    /// let total_size = gm
    ///     .iter()
    ///     .map(|region| region.len() / 1024)
    ///     .fold(0, |acc, size| acc + size);
    /// assert_eq!(3, total_size)
    /// # }
    /// ```
    fn iter(&self) -> impl Iterator<Item = &Self::R>;

    /// Applies two functions, specified as callbacks, on the inner memory regions.
    ///
    /// # Arguments
    /// * `init` - Starting value of the accumulator for the `foldf` function.
    /// * `mapf` - "Map" function, applied to all the inner memory regions. It returns an array of
    ///            the same size as the memory regions array, containing the function's results
    ///            for each region.
    /// * `foldf` - "Fold" function, applied to the array returned by `mapf`. It acts as an
    ///             operator, applying itself to the `init` value and to each subsequent elemnent
    ///             in the array returned by `mapf`.
    ///
    /// # Examples
    ///
    /// * Compute the total size of all memory mappings in KB by iterating over the memory regions
    ///   and dividing their sizes to 1024, then summing up the values in an accumulator. (uses the
    ///   `backend-mmap` feature)
    ///
    /// ```
    /// # #[cfg(feature = "backend-mmap")]
    /// # {
    /// # use vm_memory::{GuestAddress, GuestMemory, GuestMemoryRegion, GuestMemoryMmap};
    /// #
    /// let start_addr1 = GuestAddress(0x0);
    /// let start_addr2 = GuestAddress(0x400);
    /// let gm = GuestMemoryMmap::<()>::from_ranges(&vec![(start_addr1, 1024), (start_addr2, 2048)])
    ///     .expect("Could not create guest memory");
    ///
    /// let total_size = gm.map_and_fold(0, |(_, region)| region.len() / 1024, |acc, size| acc + size);
    /// assert_eq!(3, total_size)
    /// # }
    /// ```
    #[deprecated(since = "0.6.0", note = "Use `.iter()` instead")]
    fn map_and_fold<F, G, T>(&self, init: T, mapf: F, foldf: G) -> T
    where
        F: Fn((usize, &Self::R)) -> T,
        G: Fn(T, T) -> T,
    {
        self.iter().enumerate().map(mapf).fold(init, foldf)
    }

    /// Returns the maximum (inclusive) address managed by the
    /// [`GuestMemory`](trait.GuestMemory.html).
    ///
    /// # Examples (uses the `backend-mmap` feature)
    ///
    /// ```
    /// # #[cfg(feature = "backend-mmap")]
    /// # {
    /// # use vm_memory::{Address, GuestAddress, GuestMemory, GuestMemoryMmap};
    /// #
    /// let start_addr = GuestAddress(0x1000);
    /// let mut gm = GuestMemoryMmap::<()>::from_ranges(&vec![(start_addr, 0x400)])
    ///     .expect("Could not create guest memory");
    ///
    /// assert_eq!(start_addr.checked_add(0x3ff), Some(gm.last_addr()));
    /// # }
    /// ```
    fn last_addr(&self) -> GuestPhysAddr {
        self.iter()
            .map(GuestMemoryRegion::last_addr)
            .fold(GuestPhysAddr::from_usize(0), core::cmp::max)
    }

    /// Tries to convert an absolute address to a relative address within the corresponding region.
    ///
    /// Returns `None` if `addr` isn't present within the memory of the guest.
    fn to_region_addr(&self, addr: GuestPhysAddr) -> Option<(&Self::R, GuestPhysAddrRange)> {
        self.find_region(addr)
            .map(|r| (r, r.to_region_addr(addr).unwrap()))
    }

    /// Returns `true` if the given address is present within the memory of the guest.
    fn address_in_range(&self, addr: GuestPhysAddr) -> bool {
        self.find_region(addr).is_some()
    }

    /// Returns the given address if it is present within the memory of the guest.
    fn check_address(&self, addr: GuestPhysAddr) -> Option<GuestPhysAddr> {
        self.find_region(addr).map(|_| addr)
    }

    /// Check whether the range [base, base + len) is valid.
    fn check_range(&self, base: GuestPhysAddr, len: usize) -> bool {
        match self.try_access(len, base, |_, count, _, _| -> Result<usize> { Ok(count) }) {
            Ok(count) => count == len,
            _ => false,
        }
    }

    /// Returns the address plus the offset if it is present within the memory of the guest.
    fn checked_offset(&self, base: GuestPhysAddr, offset: usize) -> Option<GuestPhysAddr> {
        base.checked_add(offset as usize)
            .and_then(|addr| self.check_address(addr))
    }

    /// Invokes callback `f` to handle data in the address range `[addr, addr + count)`.
    ///
    /// The address range `[addr, addr + count)` may span more than one
    /// [`GuestMemoryRegion`](trait.GuestMemoryRegion.html) object, or even have holes in it.
    /// So [`try_access()`](trait.GuestMemory.html#method.try_access) invokes the callback 'f'
    /// for each [`GuestMemoryRegion`](trait.GuestMemoryRegion.html) object involved and returns:
    /// - the error code returned by the callback 'f'
    /// - the size of the already handled data when encountering the first hole
    /// - the size of the already handled data when the whole range has been handled
    fn try_access<F>(&self, count: usize, addr: GuestPhysAddr, mut f: F) -> Result<usize>
    where
        F: FnMut(usize, usize, GuestPhysAddrRange, &Self::R) -> Result<usize>,
    {
        let mut cur = addr;
        let mut total = 0;
        while let Some(region) = self.find_region(cur) {
            let start = region.to_region_addr(cur).unwrap();
            let cap = region.len() - start.size();
            let len = core::cmp::min(cap, (count - total) as usize);
            match f(total, len as usize, start, region) {
                // no more data
                Ok(0) => return Ok(total),
                // made some progress
                Ok(len) => {
                    total = match total.checked_add(len) {
                        Some(x) if x < count => x,
                        Some(x) if x == count => return Ok(x),
                        _ => return Err(Error::CallbackOutOfRange),
                    };
                    cur = match cur.overflowing_add(len as usize) {
                        (x, _) if x == GuestPhysAddr::from_usize(0) => x,
                        (x, false) => x,
                        (_, true) => return Err(Error::GuestAddressOverflow),
                    };
                }
                // error happened
                e => return e,
            }
        }
        if total == 0 {
            Err(Error::InvalidGuestAddress(addr))
        } else {
            Ok(total)
        }
    }

    /// Reads up to `count` bytes from an object and writes them into guest memory at `addr`.
    ///
    /// Returns the number of bytes written into guest memory.
    ///
    /// # Arguments
    /// * `addr` - Begin writing at this address.
    /// * `src` - Copy from `src` into the container.
    /// * `count` - Copy `count` bytes from `src` into the container.
    ///
    /// # Examples
    ///
    /// * Read bytes from /dev/urandom (uses the `backend-mmap` feature)
    ///
    /// ```
    /// # #[cfg(feature = "backend-mmap")]
    /// # {
    /// # use vm_memory::{Address, GuestMemory, Bytes, GuestAddress, GuestMemoryMmap};
    /// # use std::fs::File;
    /// # use std::path::Path;
    /// #
    /// # let start_addr = GuestAddress(0x1000);
    /// # let gm = GuestMemoryMmap::<()>::from_ranges(&vec![(start_addr, 0x400)])
    /// #    .expect("Could not create guest memory");
    /// # let addr = GuestAddress(0x1010);
    /// # let mut file = if cfg!(unix) {
    /// let mut file = File::open(Path::new("/dev/urandom")).expect("Could not open /dev/urandom");
    /// #   file
    /// # } else {
    /// #   File::open(Path::new("c:\\Windows\\system32\\ntoskrnl.exe"))
    /// #       .expect("Could not open c:\\Windows\\system32\\ntoskrnl.exe")
    /// # };
    ///
    /// gm.read_volatile_from(addr, &mut file, 128)
    ///     .expect("Could not read from /dev/urandom into guest memory");
    ///
    /// let read_addr = addr.checked_add(8).expect("Could not compute read address");
    /// let rand_val: u32 = gm
    ///     .read_obj(read_addr)
    ///     .expect("Could not read u32 val from /dev/urandom");
    /// # }
    /// ```
    // fn read_volatile_from<F>(&self, addr: GuestPhysAddr, src: &mut F, count: usize) -> Result<usize>
    // where
    //     F: ReadVolatile,
    // {
    //     self.try_access(count, addr, |offset, len, caddr, region| -> Result<usize> {
    //         // Check if something bad happened before doing unsafe things.
    //         assert!(offset <= count);

    //         let mut vslice = region.get_slice(caddr, len)?;

    //         src.read_volatile(&mut vslice)
    //             .map_err(GuestMemoryError::from)
    //     })
    // }

    /// Reads up to `count` bytes from guest memory at `addr` and writes them it into an object.
    ///
    /// Returns the number of bytes copied from guest memory.
    ///
    /// # Arguments
    /// * `addr` - Begin reading from this address.
    /// * `dst` - Copy from guest memory to `dst`.
    /// * `count` - Copy `count` bytes from guest memory to `dst`.
    // fn write_volatile_to<F>(&self, addr: GuestAddress, dst: &mut F, count: usize) -> Result<usize>
    // where
    //     F: WriteVolatile,
    // {
    //     self.try_access(count, addr, |offset, len, caddr, region| -> Result<usize> {
    //         // Check if something bad happened before doing unsafe things.
    //         assert!(offset <= count);

    //         let vslice = region.get_slice(caddr, len)?;

    //         // For a non-RAM region, reading could have side effects, so we
    //         // must use write_all().
    //         dst.write_all_volatile(&vslice)?;

    //         Ok(len)
    //     })
    // }

    /// Reads exactly `count` bytes from an object and writes them into guest memory at `addr`.
    ///
    /// # Errors
    ///
    /// Returns an error if `count` bytes couldn't have been copied from `src` to guest memory.
    /// Part of the data may have been copied nevertheless.
    ///
    /// # Arguments
    /// * `addr` - Begin writing at this address.
    /// * `src` - Copy from `src` into guest memory.
    /// * `count` - Copy exactly `count` bytes from `src` into guest memory.
    // fn read_exact_volatile_from<F>(
    //     &self,
    //     addr: GuestAddress,
    //     src: &mut F,
    //     count: usize,
    // ) -> Result<()>
    // where
    //     F: ReadVolatile,
    // {
    //     let res = self.read_volatile_from(addr, src, count)?;
    //     if res != count {
    //         return Err(Error::PartialBuffer {
    //             expected: count,
    //             completed: res,
    //         });
    //     }
    //     Ok(())
    // }

    /// Reads exactly `count` bytes from guest memory at `addr` and writes them into an object.
    ///
    /// # Errors
    ///
    /// Returns an error if `count` bytes couldn't have been copied from guest memory to `dst`.
    /// Part of the data may have been copied nevertheless.
    ///
    /// # Arguments
    /// * `addr` - Begin reading from this address.
    /// * `dst` - Copy from guest memory to `dst`.
    /// * `count` - Copy exactly `count` bytes from guest memory to `dst`.
    // fn write_all_volatile_to<F>(&self, addr: GuestAddress, dst: &mut F, count: usize) -> Result<()>
    // where
    //     F: WriteVolatile,
    // {
    //     let res = self.write_volatile_to(addr, dst, count)?;
    //     if res != count {
    //         return Err(Error::PartialBuffer {
    //             expected: count,
    //             completed: res,
    //         });
    //     }
    //     Ok(())
    // }

    /// Get the host virtual address corresponding to the guest address.
    ///
    /// Some [`GuestMemory`](trait.GuestMemory.html) implementations, like `GuestMemoryMmap`,
    /// have the capability to mmap the guest address range into virtual address space of the host
    /// for direct access, so the corresponding host virtual address may be passed to other
    /// subsystems.
    ///
    /// # Note
    /// The underlying guest memory is not protected from memory aliasing, which breaks the
    /// Rust memory safety model. It's the caller's responsibility to ensure that there's no
    /// concurrent accesses to the underlying guest memory.
    ///
    /// # Arguments
    /// * `addr` - Guest address to convert.
    ///
    /// # Examples (uses the `backend-mmap` feature)
    ///
    /// ```
    /// # #[cfg(feature = "backend-mmap")]
    /// # {
    /// # use vm_memory::{GuestAddress, GuestMemory, GuestMemoryMmap};
    /// #
    /// # let start_addr = GuestAddress(0x1000);
    /// # let mut gm = GuestMemoryMmap::<()>::from_ranges(&vec![(start_addr, 0x500)])
    /// #    .expect("Could not create guest memory");
    /// #
    /// let addr = gm
    ///     .get_host_address(GuestAddress(0x1200))
    ///     .expect("Could not get host address");
    /// println!("Host address is {:p}", addr);
    /// # }
    /// ```
    fn get_host_address(&self, addr: GuestPhysAddr) -> Result<*mut u8> {
        self.to_region_addr(addr)
            .ok_or(Error::InvalidGuestAddress(addr))
            .and_then(|(r, addr)| r.get_host_address(addr))
    }

    // /// Returns a [`VolatileSlice`](struct.VolatileSlice.html) of `count` bytes starting at
    // /// `addr`.
    // fn get_slice(&self, addr: GuestPhysAddr, count: usize) -> Result<VolatileSlice<MS<Self>>> {
    //     self.to_region_addr(addr)
    //         .ok_or(Error::InvalidGuestAddress(addr))
    //         .and_then(|(r, addr)| r.get_slice(addr, count))
    // }
}
