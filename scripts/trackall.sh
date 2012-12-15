#!/bin/bash

# Script for "cloning" (and tracking) all branches at codeplex.
# On Windows, this script must be executed in the "git Bash" console.
for branch in `git branch -a | grep remotes | grep -v HEAD | grep -v master`; do
    git branch --track ${branch##*/} $branch
done
git fetch --all
git pull --all
