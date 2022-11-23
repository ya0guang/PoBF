#!/bin/bash

commit="5ca2f1ebe1b057ba74438782e2bef91ec87834c4"
rust_comp="rust-src rustc-dev llvm-tools-preview rustfmt rust-analysis"
rust_toolchain=$(cat ../rust-toolchain)

git clone https://github.com/facebookexperimental/MIRAI.git $HOME/mirai || true

pushd $HOME/mirai > /dev/null
git checkout $commit
rustup override set $rust_toolchain
rustup component add --toolchain ${rust_toolchain} ${rust_comp}
cargo install --locked --path ./checker
popd > /dev/null
