.PHONY: test example notebook

test:
	@bash scripts/run_tests.sh

example:
	@wolframscript -file scripts/example_feynman.wls
