#!/usr/bin/env bash
set -euo pipefail
apt_options=(-o Acquire::Retries=3 -o Acquire::http::Timeout=30 -o Acquire::https::Timeout=30)
if [[ -f /etc/apt/apt-mirrors.txt ]]; then
  printf '%s\n' 'https://archive.ubuntu.com/ubuntu/' | sudo tee /etc/apt/apt-mirrors.txt >/dev/null
fi
sudo apt-get "${apt_options[@]}" update -y
sudo apt-get "${apt_options[@]}" install --no-install-recommends -y software-properties-common
sudo add-apt-repository --yes --no-update ppa:ubuntu-toolchain-r/test
sudo apt-get "${apt_options[@]}" update -y
sudo apt-get "${apt_options[@]}" install --no-install-recommends -y \
  cmake ninja-build g++ gcc-15 g++-15 libgmp-dev opam pkg-config python3 curl
archive="$RUNNER_TEMP/fstar.tar.gz"
curl --fail --location --retry 3 \
  "https://github.com/FStarLang/FStar/releases/download/$FSTAR_VERSION/fstar-$FSTAR_VERSION-Linux-x86_64.tar.gz" \
  --output "$archive"
printf '%s  %s\n' "$FSTAR_SHA256" "$archive" | sha256sum --check
mkdir -p "$RUNNER_TEMP/fstar-toolchain"
tar -xzf "$archive" -C "$RUNNER_TEMP/fstar-toolchain" --strip-components=2
"$RUNNER_TEMP/fstar-toolchain/bin/fstar.exe" --version
cherry_archive="$RUNNER_TEMP/fstar-cherry.tar.gz"
curl --fail --location --retry 3 \
  "https://github.com/FStarLang/FStar-nightly/releases/download/$CHERRY_FSTAR_VERSION/fstar-Linux-x86_64.tar.gz" \
  --output "$cherry_archive"
printf '%s  %s\n' "$CHERRY_FSTAR_SHA256" "$cherry_archive" | sha256sum --check
mkdir -p "$RUNNER_TEMP/fstar-cherry-toolchain"
tar -xzf "$cherry_archive" -C "$RUNNER_TEMP/fstar-cherry-toolchain" --strip-components=2
"$RUNNER_TEMP/fstar-cherry-toolchain/bin/fstar.exe" --version
gcc-15 --version
g++-15 --version
opam init --disable-sandboxing --bare --yes
opam switch create "$OPAM_SWITCH" ocaml-base-compiler.5.3.0 --yes
opam install --switch="$OPAM_SWITCH" ocamlfind zarith --yes
opam exec --switch="$OPAM_SWITCH" -- ocamlc -version
