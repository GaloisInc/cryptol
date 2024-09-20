#!/usr/bin/env bash
#
# Indicates whether the Programming Cryptol book PDF needs to be updated.
#
# Usage
# This is primarily for use in CI. You can run it locally using the following:
# > bash check_book_update.sh $(git diff --name-only --diff-filter ACDMRT master)
#
# If you are merging to a branch other than `master`, use that branch name
# instead.
#

TEX_CHANGED=0
PDF_CHANGED=0

# Examine the set of changed files to see if either the book source code
# or the book PDF were changed.
for fname in $@ ; do
    case $fname in
        docs/ProgrammingCryptol/*)
            TEX_CHANGED=1
            TEX_FILES="$TEX_FILES$fname " ;;
        docs/ProgrammingCryptol.pdf)
            PDF_CHANGED=1 ;;
    esac
done

if (($TEX_CHANGED)) && ((! $PDF_CHANGED)); then
    echo -e "Changed files: $TEX_FILES"
    echo "The Programming Cryptol source code changed, but the PDF was"
    echo "not updated. Please rebuild the book to incorporate your changes"
    echo "and copy the file to 'docs/ProgrammingCryptol.pdf'."
    exit 1
elif (($TEX_CHANGED)) && (($PDF_CHANGED)); then
    echo "Thanks for updating the PDF along with your changed source code!"
    echo "This CI job doesn't check that you incorporated all the source"
    echo "changes into the PDF; please confirm that it's properly updated"
    echo "before merging."
    exit 0
elif ((! $TEX_CHANGED)) && (($PDF_CHANGED)); then
    echo "The Programming Cryptol PDF changed but there was no corresponding"
    echo "change to the source code."
    exit 1
else
    echo "There were no changes to the book. No action needed."
    exit 0
fi
