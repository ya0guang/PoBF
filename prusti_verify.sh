#!/bin/bash
prusti_path="~/prusti-dev/target/release/"
cargo_prusti="${prusti_path}cargo-prusti"
config="PRUSTI_CHECK_OVERFLOWS=true PRUSTI_LOG=info PRUSTI_NO_VERIFY_DEPS=true"

echo "Doing verification on the PoBF framework..."
eval "${config} ${cargo_prusti} --features use_prusti,sgx"

