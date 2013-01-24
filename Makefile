CC=clang
CFLAGS=
LDFLAGS=
EXEC=test.exe
LIBS=string.o

FRAMAC=frama-c
FRAMACFLAGS=-wp -wp-rte -wp-warnings

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
