#!/usr/bin/env bash

z3_git_version() {
  if [ -n "${Z3_GIT_VERSION}" ]; then
    echo "${Z3_GIT_VERSION}"
  else
    COMMIT_HASH="$(git rev-parse HEAD)"
    if [ -z "${COMMIT_HASH}" ]; then
       echo "Not a git repository" 1>&2
       exit 1
    fi
    COMMIT_DATE="$(git show -s --format=%ci | awk '{ print $1 }')"
    echo "${COMMIT_DATE}-${COMMIT_HASH}"
  fi
}

