#!/bin/bash

# Automated proof iteration script using Claude CLI
# Usage: ./auto-iterate-claude.sh [iteration_number] [target]

set -e

ITERATION=${1:-13}
TARGET=${2:-"Prove the general k case for Erdős Problem 361"}
PROBLEM_DIR="problem-361"
PROOF_LOG="$PROBLEM_DIR/proof-log"
LEAN_FILE="$PROOF_LOG/iteration-$(printf '%03d' $ITERATION).lean"
ATTEMPT_FILE="$PROOF_LOG/iteration-$(printf '%03d' $ITERATION)-attempt.md"
PROMPT_FILE="$PROOF_LOG/iteration-$(printf '%03d' $ITERATION)-prompt.md"

echo "=== Erdős Problem 361 - Automated Proof Loop with Claude ==="
echo "Iteration: $ITERATION"
echo "Target: $TARGET"
echo "Lean file: $LEAN_FILE"
echo ""

# Create the prompt file
cat > "$PROMPT_FILE" << EOF
You are working on Erdős Problem 361 through Lean formalization.

Target for this iteration:
$TARGET

Lean file to create or update:
$LEAN_FILE

Local context:
- Problem: For fixed c > 0 and large n, find the maximum size of A ⊆ {1,...,floor(cn)} such that n is not a subset sum of A.
- c ≥ 1 case: F_c(n) = floor(cn) - ceil(n/2) (proven)
- k=1 case: Interval [(n+1)/2, n-1] is admissible (proven)
- General k case: Interval [n/(k+1), n/k] should be admissible (key insight documented)

Previous iterations:
- iteration-010: k=1 admissibility proven
- iteration-012: General k insight documented

Produce:
1. A precise Lean theorem or lemma statement.
2. A Lean proof attempt as the first fenced code block.
3. Any imports required.
4. A list of all floor, parity, endpoint, and large-n obligations.
5. The weakest formalization step.
6. A suggested narrower Lean target if the proof fails.
EOF

# Call Claude CLI to generate the proof attempt
echo "Calling Claude CLI to generate proof attempt..."
if command -v claude &> /dev/null; then
    claude -p "$(cat $PROMPT_FILE)" > "$ATTEMPT_FILE" 2>&1 || true
else
    echo "Claude CLI not found. Creating placeholder attempt."
    echo "Claude CLI not found. Please install Claude CLI or manually create the attempt." > "$ATTEMPT_FILE"
fi

# Extract Lean code from the attempt file
echo "Extracting Lean code from attempt..."
if grep -q '```lean' "$ATTEMPT_FILE"; then
    sed -n '/```lean/,/```/p' "$ATTEMPT_FILE" | sed '1d;$d' > "$LEAN_FILE"
else
    echo "No Lean code block found in attempt. Creating placeholder."
    echo "-- Placeholder for iteration $ITERATION" > "$LEAN_FILE"
    echo "-- Target: $TARGET" >> "$LEAN_FILE"
    echo "" >> "$LEAN_FILE"
    echo "/-- Placeholder theorem -/" >> "$LEAN_FILE"
    echo "theorem placeholder : True := by" >> "$LEAN_FILE"
    echo "  trivial" >> "$LEAN_FILE"
fi

# Compile the Lean file
echo "Compiling Lean file..."
lean_output=$(lean "$LEAN_FILE" 2>&1) || true
echo "$lean_output"

# Check if compilation succeeded
if echo "$lean_output" | grep -q "error"; then
    echo "❌ Compilation failed"
    # Add compilation output to attempt file
    echo "" >> "$ATTEMPT_FILE"
    echo "## Lean Check" >> "$ATTEMPT_FILE"
    echo "" >> "$ATTEMPT_FILE"
    echo "- **Command**: \`lean $LEAN_FILE\`" >> "$ATTEMPT_FILE"
    echo "- **Output**: $lean_output" >> "$ATTEMPT_FILE"
    echo "- **Status**: ❌ Compilation failed" >> "$ATTEMPT_FILE"
else
    echo "✅ Compilation succeeded"
    # Add compilation output to attempt file
    echo "" >> "$ATTEMPT_FILE"
    echo "## Lean Check" >> "$ATTEMPT_FILE"
    echo "" >> "$ATTEMPT_FILE"
    echo "- **Command**: \`lean $LEAN_FILE\`" >> "$ATTEMPT_FILE"
    echo "- **Output**: $lean_output" >> "$ATTEMPT_FILE"
    echo "- **Status**: ✅ Compiled successfully" >> "$ATTEMPT_FILE"
fi

echo ""
echo "=== Iteration $ITERATION Complete ==="
echo "Files created:"
echo "  - $PROMPT_FILE"
echo "  - $ATTEMPT_FILE"
echo "  - $LEAN_FILE"
echo ""
echo "Next steps:"
echo "  1. Review the proof attempt"
echo "  2. If compilation failed, fix the Lean code"
echo "  3. Run: ./auto-iterate-claude.sh $((ITERATION + 1)) 'Next target'"
