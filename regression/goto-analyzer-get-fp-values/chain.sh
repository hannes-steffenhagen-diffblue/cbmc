GotoAnalyzerPath=$1
echo "GotoAnalyzerPath = $GotoAnalyzerPath"
GotoCCPath=$2
echo "GotoCCPath = $GotoCCPath"
GotoInstrumentPath=$3
echo "GotoInstrumentPath = $GotoInstrumentPath"
CBMCPath=$4
echo "CBMCPath = $CBMCPath"
TestCPath=$5
echo "TestCPath = $TestCPath"
TestJSONPath=$(mktemp);
GotoBinaryPath="$(mktemp)"
GotoBinaryModPath="$(mktemp)"

# Set up pipeline
# goto-cc produces temporary goto binary from C file
# goto-analyzer produces json file with restrictions
# goto-instrument produces new gb with old gb + restrictions
# cbmc runs on final gb

# purpose: This lets us test end-to-end that all stages of the pipeline are compatible with
# each other, and that they produce the output we expect

$GotoCCPath $TestCPath -o $GotoBinaryPath

$GotoAnalyzerPath \
   '--verify' $GotoBinaryPath \
   '--get-fp-values' $TestJSONPath \
   '--variable-sensitivity' \
   '--value-set' \
   > /dev/null \
   2> /dev/null

$GotoInstrumentPath \
  --function-pointer-restrictions-file $TestJSONPath \
  $GotoBinaryPath $GotoBinaryModPath

$CBMCPath $GotoBinaryModPath --pointer-check
  
cat $TestJSONPath

rm $TestJSONPath
rm $GotoBinaryPath
rm $GotoBinaryModPath