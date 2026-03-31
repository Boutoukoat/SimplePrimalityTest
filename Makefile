

GGG = g++ -O3 -Wall -march=native -fomit-frame-pointer -fexpensive-optimizations
# GGG = clang++ -O3 -Wall -march=native -fomit-frame-pointer

OBJ = simple_primality_main.o \
      simple_primality.o \
      simple_primality_alloc.o \
      simple_primality_precompute.o \
      expression_parser.a

simple: $(OBJ)
	$(GGG) -static -o simple $(OBJ) -lgmp -lpthread -lm

simple_primality_main.o: simple_primality_main.cpp simple_primality.h simple_primality_alloc.h bison.gmp_expr.tab.h
	$(GGG) -c -o simple_primality_main.o simple_primality_main.cpp

simple_primality_alloc.o: simple_primality_alloc.cpp simple_primality_alloc.h
	$(GGG) -c -o simple_primality_alloc.o simple_primality_alloc.cpp

simple_primality.o: simple_primality.cpp simple_primality.h
	$(GGG) -c -o simple_primality.o simple_primality.cpp

expression_parser.a : bison.gmp_expr.o lex.gmp_expr.o bison.gmp_expr.tab.h
	ar vr expression_parser.a bison.gmp_expr.o lex.gmp_expr.o

bison.gmp_expr.o : bison.gmp_expr.tab.c bison.gmp_expr.h
	$(GGG) -c -o bison.gmp_expr.o bison.gmp_expr.tab.c

bison.gmp_expr.tab.c bison.gmp_expr.tab.h : parser.y
	bison -d parser.y

lex.gmp_expr.o : lex.gmp_expr.c
	$(GGG) -Wno-unused-function -c -o lex.gmp_expr.o lex.gmp_expr.c

lex.gmp_expr.c : parser.l bison.gmp_expr.tab.h
	flex parser.l

check: simple
	./simple -st

clean:
	rm -f ./simple $(OBJ) bison.gmp_expr.o bison.gmp_expr.tab.c bison.gmp_expr.tab.h lex.gmp_expr.o lex.gmp_expr.c


