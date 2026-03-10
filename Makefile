# This Makefile is for convenience as a reminder and shortcut for the most used commands

# Package folder
PACKAGE = amortizedHGM

# change to your sage command if needed
SAGE = sage

all: install test

install:
	$(SAGE) -pip install --no-build-isolation -e .

test:
	$(SAGE) -t --force-lib $(PACKAGE)

coverage:
	$(SAGE) -coverage $(PACKAGE)/*

doc:
	cd docs && $(SAGE) -sh -c "make html"

doc-pdf:
	cd docs && $(SAGE) -sh -c "make latexpdf"

clean:
	rm -rf build dist *.egg-info
	rm -rf $(PACKAGE)/*.c

.PHONY: all install test coverage clean doc doc-pdf
