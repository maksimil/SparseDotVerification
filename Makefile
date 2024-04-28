check:
	frama-c -rte -wp -wp-prover altergo,z3 -cpp-extra-args="-I./include" src/*
