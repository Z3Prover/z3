#!/usr/bin/env bash

REPO_ROOT="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"
. "${REPO_ROOT}/common.sh"

z3_version() {
  local UBUNTU_VERSION_STRING="x64-ubuntu-$(lsb_release -rs)"
  echo "z3-${Z3_GIT_VERSION}-${UBUNTU_VERSION_STRING}"
}

ubuntu_zip_name() {
  echo "$(z3_version).zip"
}

linux_zip_name() {
  Z3_GIT_VERSION="$(z3_git_version)"
  PLATFORM_STRING="$(python -mplatform)"
  if [[ "${PLATFORM_STRING}" = *"Ubuntu"* ]]; then
     ubuntu_zip_name
  else
     echo "Unsupported platform: ${PLATFORM_STRING}" 1>&2
     exit 1
  fi
}

