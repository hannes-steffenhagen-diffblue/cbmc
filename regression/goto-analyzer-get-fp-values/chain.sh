GotoAnalyzerPath=$1
TestCPath=$2
TestJSONPath=$(mktemp);

$GotoAnalyzerPath \
   '--verify' $TestCPath \
   '--get-fp-values' $TestJSONPath \
   '--variable-sensitivity' \
   '--value-set' \
   > /dev/null \
   2> /dev/null

cat $TestJSONPath
rm $TestJSONPath