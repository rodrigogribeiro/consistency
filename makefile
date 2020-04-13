target: all

all : consistency.lagda latex/Makefile
	agda consistency.lagda --latex
	$(MAKE) -C latex

clean:
	rm *.agdai
	$(MAKE) -C latex clean
