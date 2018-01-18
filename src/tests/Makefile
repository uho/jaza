TESTSRC=$(wildcard *.jaza)
TESTS=$(TESTSRC:.jaza=.out)

# If you have a compiled (GHC) version of Jaza:
JAZA=../jaza

# If you have an interpreted (Hugs) version of Jaza:
# JAZA=runhugs ../TextUI.hs

%.out: %.jaza
	$(JAZA) <$*.jaza >$*.out
	@if grep Error $*.out; then echo ERROR FOUND; else echo Passed; fi

# This translates Jaza tests into tests for CLPS-BZ (another evaluator).
%.clps: %.jaza ../clpstests
	../clpstests <$*.jaza >$*.clps


help:
	@echo "  make tests       -- run all Jaza tests, using $(JAZA)"
	@echo "  make count       -- count the number of tests."
	@echo "  make clean       -- remove all derived files"
	@echo ""
	@echo "  make clps        -- translate Jaza tests to CLPS syntax"
	@echo "  make clpscopy    -- save a copy of CLPS tests"
	@echo "  make clpsdiff    -- compare CLPS tests with saved copy"

tests: ${TESTS}

# This defines which *.jaza test files are worth translating for CLPS-BZ.
CLPSTESTS=sets.clps integers.clps relations.clps misc.clps

clps: $(CLPSTESTS)
	@echo "All .clps files are up to date"

clpscopy:
	for c in $(CLPSTESTS); do cp "$$c" "$$c.old"; done

clpsdiff:
	for c in $(CLPSTESTS); do echo "$$c"; diff -b "$$c.old" "$$c"; done

count:
	@for j in *.jaza; do echo "$$(grep '^check' $$j | wc -l)  $$j"; done
	@echo "  =====  =============="
	@echo "$$(grep '^check' *.jaza | wc -l)  Total"

clean:
	-rm -f $(TESTS) $(CLPSTESTS)
