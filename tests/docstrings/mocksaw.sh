#!/usr/bin/env sh

saw_file=$(printf '%s\n' "$1" | tr '\\' '/')
saw_name=${saw_file##*/}
import_path=$(printf '%s\n' "$SAW_IMPORT_PATH" | tr '\\' '/')

if [ "$#" = 4 ] &&
   [ "$saw_name" = "T13.saw" ] &&
   [ "$2" = "1" ] &&
   [ "$3" = "two words" ] &&
   [ "$4" = "3" ] ; then
    echo "This successful output should be hidden"
    exit 0
fi
if [ "$saw_name" = "T14.saw" ] ; then
    echo "SAW failed to process T14.saw" >&2
    exit 1
fi
if [ "$saw_name" = "T16.saw" ] &&
   [ -z "$import_path" ] ; then
    case "$saw_file" in
        */tests/docstrings/T16/T16.saw) exit 0 ;;
    esac
fi
if [ "$saw_name" = "T17.saw" ] &&
   [ "$import_path" = "./proofs" ] ; then
    case "$saw_file" in
        */tests/docstrings/proofs/T17.saw) exit 0 ;;
    esac
fi

exit 1
