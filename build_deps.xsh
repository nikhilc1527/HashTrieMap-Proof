#!/usr/bin/env xonsh

# recursively uses rocq dep to get dependencies only of files that are needed, until there are no more dependencies to find
# speeds up `make clean; make` down from ~20 min to ~7 min by avoiding building the entirety of perennial, which has a lot of files are unnecessarily built by default
# written in xonsh shell because its fun, should probably be rewritten in python to be portable (not everyone has xonsh installed, should be very easy to rewrite in python)
# there must be a way to do this with just rocq dep (or separate package), but I couldn't find it

usage = "usage: ./rocq_deps_rec.xsh [rocq dep args...] -- <files...>"

if len($ARGS) <= 1:
    print(usage)
    exit(1)

$ARGS = $ARGS[1:]
try:
    ind = ($ARGS).index("--")
    rocqdep_args = ($ARGS[:ind])
    source_files = set($ARGS[ind+1:])
except ValueError:
    print(usage)
    exit(1)

if len(source_files) == 0:
    print(usage)
    exit(1)

rocqdep = $(rocq dep @(rocqdep_args) @(source_files))

def expand_src(src, rd):
    new_src = set()
    for line in rd.splitlines():
        snd = line.partition(":")[-1]
        # new_src |= set(snd.split())
        for s in snd.split():
            (base, _, ext) = s.partition(".")
            if ext.startswith("v"):
                new_src.add(base + ".v")
    return new_src

new_source_files = expand_src(source_files, rocqdep)
# print(new_source_files)

while new_source_files != source_files:
    source_files = new_source_files
    rocqdep = $(rocq dep @(rocqdep_args) @(source_files))
    new_source_files = expand_src(source_files, rocqdep)
    # print(new_source_files)

print(rocqdep)
