#!/bin/bash

# Copyright (c) 2022 Haobin Chen and Hongbo Chen
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

commit="b74ed28a0d8b946c67fb85f56edbeb81346aabd9"
rust_comp="rust-src rustc-dev llvm-tools-preview rustfmt rust-analysis"
nightly="nightly-2022-02-11"

# Clone this repo.
git clone https://github.com/viperproject/prusti-dev.git $HOME/prusti-dev

pushd $HOME/prusti-dev
# Use this specific commit.
git checkout ${commit}

echo "[+] Preparing the Rust toolkit..."
rustup override set ${nightly}
rustup component --toolchain ${nightly} ${rust_comp}
echo "[-] Rust toolkit successfully configured!"
./x.py setup && ./x.py buil;d --release
popd

echo "Installation finished."
echo "You can now execute 'prusti' on the crate from 'verify' branch by"
echo "   PRUSTI_CHECK_OVERFLOWS=true PRUSTI_LOG=info PRUSTI_NO_VERIFY_DEPS=true PRUSTI_ASSERT_TIMEOUT=10000 $HOME/prusti-dev/target/release/cargo-prusti --features sgx,use_prusti"