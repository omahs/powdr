extern "C" {
    // This is a dummy implementation of Poseidon hash,
    // which will be replaced with a call to the Poseidon
    // coprocessor during compilation.
    // The function itself will be removed by the compiler
    // during the reachability analysis.
    fn poseidon_gl_coprocessor(data: *mut [u64; 12]);

    // This will be replaced by a call to prover input.
    fn input_coprocessor(index: u32, channel: u32) -> u32;
}

extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;

pub fn get_data(channel: u32, data: &mut [u32]) {
    for (i, d) in data.iter_mut().enumerate() {
        *d = unsafe { input_coprocessor(channel, (i + 1) as u32) };
    }
}

pub fn get_data_len(channel: u32) -> usize {
    unsafe { input_coprocessor(channel, 0) as usize }
}

use serde::de::DeserializeOwned;

pub fn get_data_serde<T: DeserializeOwned>(channel: u32) -> T {
    let l = get_data_len(channel);
    let mut data = vec![0; l];
    get_data(channel, &mut data);

    // TODO this extra conversion can be removed if we change everything to be u8
    let data: Vec<u8> = data.into_iter().map(|x| x as u8).collect();

    serde_cbor::from_slice(&data.as_slice()).unwrap()
}

const GOLDILOCKS: u64 = 0xffffffff00000001;

/// Calls the low level Poseidon coprocessor in PIL, where
/// the last 4 elements are the "cap"
/// and the return value is placed in data[0:4].
/// The safe version below also checks that each u64 element
/// is less than the Goldilocks field.
/// The unsafe version does not perform such checks.
pub fn poseidon_gl(mut data: [u64; 12]) -> [u64; 4] {
    for &n in data.iter() {
        assert!(n < GOLDILOCKS);
    }

    unsafe {
        poseidon_gl_coprocessor(&mut data as *mut [u64; 12]);
    }

    [data[0], data[1], data[2], data[3]]
}

pub fn poseidon_gl_unsafe(mut data: [u64; 12]) -> [u64; 4] {
    unsafe {
        poseidon_gl_coprocessor(&mut data as *mut [u64; 12]);
    }

    [data[0], data[1], data[2], data[3]]
}
