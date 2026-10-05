#!/usr/bin/env sh

if [ "$1" = "T13.saw" ] ; then
    echo "This successful output should be hidden"
    exit 0
fi
if [ "$1" = "T14.saw" ] ; then
    echo "SAW failed to process T14.saw" >&2
    exit 1
fi

exit 1
