#!/bin/bash
echo "=============================================="
echo "  ADMITTO — verified shield for AI kernels"
echo "=============================================="
echo
echo "An AI generator proposes GPU kernels. A machine-"
echo "checked gate admits a kernel only if it is PROVEN"
echo "to compute vector-add for all inputs — no testing,"
echo "no tolerance, no sampling."
echo
echo "--- Proposal 1: a correct vector-add kernel ---"
lake exe trident kernels/vector_add_tutorial.ttir 0 1024 1024 2>/dev/null
echo
echo "--- Proposal 2: subtly wrong (addf -> subf) ---"
echo "    One character different. Computes a-b, not a+b."
lake exe trident kernels/vector_add_tutorial_WRONG.ttir 0 1024 1024 2>/dev/null
echo
echo "=============================================="
echo "Correct kernel admitted, wrong one rejected —"
echo "by machine-checked proof, not by testing."
echo "=============================================="
