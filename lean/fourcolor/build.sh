#!/bin/bash
# CPU-friendly build wrapper
# Resource policy is supplied by the caller.
if [ -z "$1" ]; then
    echo "Usage: ./build.sh <target>"
    echo "Example: ./build.sh FourColor.Geometry.DualForest"
    exit 1
fi

echo "Building $1..."
lake build "$@"
