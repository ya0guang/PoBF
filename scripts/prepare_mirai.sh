#!/bin/bash

rust_comp="rust-src rustc-dev llvm-tools-preview rustfmt rust-analysis"
rust_toolchain=$(awk '$1 == "channel" {print $3}' ../rust-toolchain | tr -d \")

git clone https://github.com/hiroki-chen/MIRAI.git $HOME/mirai || true

pushd $HOME/mirai > /dev/null
rustup override set $rust_toolchain
rustup component add --toolchain ${rust_toolchain} ${rust_comp}
cargo install --locked --path ./checker
popd > /dev/null
