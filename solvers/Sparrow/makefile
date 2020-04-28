CC=gcc
CFLAGSO= -Wall -Wextra -static -Og -funroll-loops -fexpensive-optimizations -std=c99 -ggdb
CFLAGSD=  -pg -ggdb -Wall -lm   -Wno-missing-braces -static 

all: sparrow #sparrownX

sparrow:	sparrow.c
			$(CC) $(CFLAGSO) -DXOR sparrow.c  -lm -o sparrow

sparrowp:	sparrow.c
			$(CC) $(CFLAGSO) -DXOR sparrow.c  -lm -o sparrowp -DUSE_PREDICT


sparrownX:	sparrow.c
			$(CC) $(CFLAGSO)  sparrow.c -lm -o sparrownX			
			
debug:	sparrow.c
			$(CC) $(CFLAGSD)  -DXOR sparrow.c -lm -o sparrow
						
clean:	
		rm -f *.o *.a *.so
		rm -f sparrow
		rm -f sparrownX

