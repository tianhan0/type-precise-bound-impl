#!/bin/sh

for f in *.c; do 
    mv -- "$f" "${f%.c}.java"
done
