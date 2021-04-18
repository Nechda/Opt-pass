# Required packages:
# clang-11 libstdc++-8-dev gcc-aarch64-linux-gnu g++-aarch64-linux-gnu qemu-user
CC=clang-11
CXX=clang++-11
OPT=opt-11
LLVM_CONFIG=llvm-config-11
LLC=llc-11
QEMU_USER=qemu-aarch64
QEMU_LD_PREFIX=/usr/aarch64-linux-gnu
BENCH_ARG=17

CFLAGS=-O2 -Werror -Wall -pedantic -fno-inline-functions -fPIC
CFLAGS_CROSS=-I$(QEMU_LD_PREFIX)/include -target aarch64-linux-gnu -ffixed-x28
LDLIBS=-lm

BENCH=quadratic
BENCH_REF=$(BENCH).ref
BENCH_OPT=$(BENCH).opt
OUTPUT_REF=out.ref
OUTPUT_OPT=out.opt
PASS_NAME=reg_inserter
N_TESTS = 128

$(BENCH_REF): $(BENCH).c
	$(CC) $(CFLAGS) $(CFLAGS_CROSS) $(LDLIBS) -o $@ $<

$(PASS_NAME).so: $(PASS_NAME).cpp
	$(CXX) $(CFLAGS) `$(LLVM_CONFIG) --cxxflags` -shared -fPIC -o $@ $<

$(BENCH_OPT): $(BENCH).c $(PASS_NAME).so
	$(CC) $(CFLAGS) $(CFLAGS_CROSS) -S -emit-llvm -o $(BENCH).orig.ll $<
	$(OPT) -load ./$(PASS_NAME).so -S -$(PASS_NAME) < $(BENCH).orig.ll > $(BENCH).ll
	$(LLC) -O2 --relocation-model=pic -o $(BENCH).s $(BENCH).ll
	$(CC) $(CFLAGS_CROSS) $(LDLIBS) $(BENCH).s -o $@

.PHONY: run-ref
run-ref: $(BENCH_REF)
	time -p $(QEMU_USER) -L $(QEMU_LD_PREFIX) ./$(BENCH_REF) $(BENCH_ARG) > $(OUTPUT_REF)

.PHONY: run-opt
run-opt: $(BENCH_OPT)
	time -p $(QEMU_USER) -L $(QEMU_LD_PREFIX) ./$(BENCH_OPT) $(BENCH_ARG) > $(OUTPUT_OPT)

.PHONY: compare
compare: run-ref run-opt
	diff $(OUTPUT_REF) $(OUTPUT_OPT)

.PHONY: test
test: tester.out
	./tester.out $(N_TESTS)

tester.out: t/ir_generator.cpp $(PASS_NAME).cpp
	$(CXX) $(CFLAGS) `$(LLVM_CONFIG) --cxxflags` -g -fsanitize=address -lLLVM-11 \
	t/ir_generator.cpp $(PASS_NAME).cpp -o tester.out


.PHONY: clean
clean:
	rm -f $(BENCH_REF) $(OUTPUT_REF) \
	      $(PASS_NAME).so \
	      $(BENCH).orig.ll $(BENCH).ll $(BENCH).s $(BENCH_OPT) $(OUTPUT_OPT) \
		  tester.out


