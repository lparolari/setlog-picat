# BIN: output directory for compiled test files.
# SOURCES: sources files.
# TESTS: tests files.
# PICAT: picat interpreter.
# EXEC: test execution script.

BIN=bin
SOURCES=../src/*
TESTS=*_test.pi
PICAT=picat
EXEC=go_tests

all: tests

tests:
	mkdir -p $(BIN)
	cp -rf $(SOURCES) $(BIN)
	cp -f $(TESTS) $(BIN)
	echo "$(PICAT) $(BIN)/solver_test.pi" > $(EXEC)
	chmod a+x $(EXEC)

clear:
	rm -f $(EXEC)
	rm -rf $(BIN)