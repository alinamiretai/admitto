#!/usr/bin/env python3
import sys, re

def clean_ttir(src):
    lines = []
    for line in src.splitlines():
        line = line.strip()
        if re.match(r'%\w+ = ', line) or re.match(r'tt\.store', line):
            line = re.sub(r' loc\([^)]*\)', '', line)
            lines.append(line)
    return '\n'.join(lines)

src = open(sys.argv[1]).read()
print(clean_ttir(src))
