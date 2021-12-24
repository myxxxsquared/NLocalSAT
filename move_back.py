
import sys

src = sys.argv[1]
dst = sys.argv[2]

srcfile = open(src, 'r')
dstfile = open(dst, 'a')


dstfile.write('\n')
for line in srcfile:
    if line.startswith('p '):
        dstfile.write(line)
