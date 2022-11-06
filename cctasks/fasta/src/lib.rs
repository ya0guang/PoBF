// Copyright (C) 2017-2018 Baidu, Inc. All Rights Reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
//
//  * Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
//  * Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in
//    the documentation and/or other materials provided with the
//    distribution.
//  * Neither the name of Baidu, Inc., nor the names of its
//    contributors may be used to endorse or promote products derived
//    from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;
#[cfg(feature = "sgx")]
use sgx_types::error::SgxResult;

#[cfg(not(feature = "sgx"))]
type SgxResult<T> = std::result::Result<T, Box<dyn std::error::Error>>;

const LINE_LENGTH: usize = 60;
const BLOCK_SIZE: usize = LINE_LENGTH * 1024;
const IM: u32 = 139968;

/// Pseudo-random number generator
struct Rng(u32);

impl Rng {
    fn new() -> Self {
        Rng(42)
    }

    fn gen(&mut self, probabilities: &[(u32, u8)], block: &mut [u8]) {
        for i in block.iter_mut() {
            self.0 = (self.0 * 3877 + 29573) % IM;
            *i = probabilities.iter().find(|&&(p, _)| p >= self.0).unwrap().1;
        }
    }
}

/// From a probability distribution, generate a cumulative probability distribution.
fn cumulative_probabilities(ps: &[(char, f32)]) -> Vec<(u32, u8)> {
    ps.iter()
        .scan(0., |sum, &(c, p)| {
            *sum += p;
            Some(((*sum * IM as f32).floor() as u32, c as u8))
        })
        .collect()
}

/// Output FASTA data from the provided generator function.
fn make_fasta<F>(n: usize, mut f: F) -> SgxResult<Vec<u8>>
where
    F: FnMut(&mut [u8]),
{
    let mut block = vec![0; BLOCK_SIZE];

    // Write whole blocks.
    let num_blocks = n / BLOCK_SIZE;
    for _ in 0..num_blocks {
        f(&mut block);
    }

    // Write trailing block.
    let trailing_len = n % BLOCK_SIZE;
    if trailing_len > 0 {
        f(&mut block[..trailing_len]);
    }

    Ok(block)
}

pub fn private_computation(input: Vec<u8>) -> Vec<u8> {
    let n = usize::from_ne_bytes(input[..4].try_into().unwrap());
    // Generate a DNA sequence by copying from the given sequence.
    let mut it = input[4..].iter().cloned().cycle();

    let mut ans = make_fasta(n * 2, |block| {
        for i in block {
            *i = it.next().unwrap()
        }
    }).unwrap();

    // Generate DNA sequences by weighted random selection from two alphabets.
    let p0 = cumulative_probabilities(&[
        ('a', 0.27),
        ('c', 0.12),
        ('g', 0.12),
        ('t', 0.27),
        ('B', 0.02),
        ('D', 0.02),
        ('H', 0.02),
        ('K', 0.02),
        ('M', 0.02),
        ('N', 0.02),
        ('R', 0.02),
        ('S', 0.02),
        ('V', 0.02),
        ('W', 0.02),
        ('Y', 0.02),
    ]);
    let p1 = cumulative_probabilities(&[
        ('a', 0.3029549426680),
        ('c', 0.1979883004921),
        ('g', 0.1975473066391),
        ('t', 0.3015094502008),
    ]);

    let mut rng = Rng::new();

    ans.extend_from_slice(&make_fasta(n * 3, |block| rng.gen(&p0, block)).unwrap());
    ans.extend_from_slice(&make_fasta(n * 5, |block| rng.gen(&p1, block)).unwrap());

    ans
}
