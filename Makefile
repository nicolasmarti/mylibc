CC=clang
CFLAGS=
LDFLAGS=
EXEC=test.exe
LIBS=basetype.o string.o

PROVERS= alt-ergo,coq #,zenon,z3,coqide

FRAMAC=frama-c
FRAMACFLAGS=-wp -wp-rte -wp-warnings -wp-proof $(PROVERS) -wp-out proofs -wp-script proof.v  #-wp-print

all: $(EXEC)

%.o: %.c %.h
	@echo "****************************************************"
	@echo $<
	@echo "****************************************************"
	$(FRAMAC) $(FRAMACFLAGS) $< -then -werror-no-no-unknown -werror -werror-no-external 
	@echo "------------------------------------"
	$(CC) -c -o $@ $(CFLAGS) $<
	@echo "\n\n"

%.o: %.c
	@echo "****************************************************"
	@echo $<
	@echo "****************************************************"
	$(FRAMAC) $(FRAMACFLAGS) $<
	@echo "------------------------------------"
	$(CC) -c -o $@ $(CFLAGS) $<
	@echo "\n\n"

%.exe: %.o $(LIBS) 
	$(CC) $(CFLAGS) $^ $(LDFLAGS) -o $@

clean:
	rm -Rf $(LIBS) $(EXEC)


gui:
	frama-c-gui $(FRAMACFLAGS) $1