#!/bin/bash

SCRIPT_DIR="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"
. ${SCRIPT_DIR}/run_quiet.sh

set -x
set -e
set -o pipefail

run_quiet brew update
export HOMEBREW_NO_AUTO_UPDATE=1

function brew_install_or_upgrade() {
  if brew ls --versions "$1" > /dev/null 2>&1 ; then
    brew upgrade "$1"
  else
    brew install "$1"
  fi
}

# FIXME: We should fix the versions of dependencies used
# so that we have reproducible builds.

# HACK: Just use CMake version in TravisCI for now
if [ "X${MACOS_UPDATE_CMAKE}" = "X1" ]; then
  brew_install_or_upgrade cmake
fi

if [ "X${Z3_CMAKE_GENERATOR}" = "XNinja" ]; then
  brew_install_or_upgrade ninja
fi

if [ "X${Z3_USE_LIBGMP}" = "X1" ]; then
  brew_install_or_upgrade gmp
fi

if [ "X${BUILD_DOCS}" = "X1" ]; then
  brew_install_or_upgrade doxygen
fi

if [ "X${DOTNET_BINDINGS}" = "X1" ]; then
  brew_install_or_upgrade mono
fi

if [ "X${JAVA_BINDINGS}" = "X1" ]; then
  brew cask install java
fi
