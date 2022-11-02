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

commit="ee91e7772e764c910b1e6638f609ad5da0a791a7"
rust_comp="rust-src rustc-dev llvm-tools-preview rustfmt rust-analysis"
rust_toolchain=$(cat ./rust-toolchain)

# Clone this repo.
git clone https://github.com/viperproject/prusti-dev.git $HOME/prusti-dev

pushd $HOME/prusti-dev
# Use this specific commit.
git checkout ${commit}
printf '[toolchain]\nchannel = "nightly-2022-10-22"\ncomponents = [ "rustc-dev", "llvm-tools-preview", "rust-std", "rustfmt", "clippy" ]\nprofile = "minimal"' \
  > rust-toolchain
echo "[+] Preparing the Rust toolkit..."
rustup component add --toolchain ${rust_toolchain} ${rust_comp}
echo "[+] Rust toolkit successfully configured!"
./x.py setup && ./x.py build --release
mkdir -p $HOME/.cargo/prusti && ./x.py package release $HOME/.cargo/prusti
echo "[+] Prusti is installed to $HOME/.cargo/prusti"
popd

echo "[+] Installation finished."
echo "[+] You can now execute 'Prusti' on the pobf_state crate by"
echo "   cargo-prusti --features sgx,prusti"
