if ! command -v python3 > /dev/null; then
    echo "python3 not found: traces not validated against XSD"
    exit 1
fi

python_minor_version=$(python3 --version | cut -d ' ' -f 2 | cut -d '.' -f 2)

if [ $python_minor_version -lt 5 ]; then
    echo "python version less than 3.5: traces not validated against XSD"
    exit 1
fi

xmllint="$(command -v xmllint)"
if [ $? -ne 0 ] > /dev/null; then
    echo "xmllint not found: traces not validated against XSD"
    exit 1
fi

python3 check.py ../../src/cbmc/cbmc "$xmllint"
