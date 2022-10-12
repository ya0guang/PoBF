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

git clone https://github.com/viperproject/prusti-dev.git $HOME

pushd $HOME/prusti-dev
git checkout b74ed28a0d8b946c67fb85f56edbeb81346aabd9
rustup override set nightly-2022-02-11
rustup component --toolchain nightly-2022-02-11 rust-src rustc-dev llvm-tools-preview rustfmt rust-analysis
./x.py setup && ./x.py buil;d --release
popd