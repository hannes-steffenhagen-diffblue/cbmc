if ! command -v python3 > /dev/null; then
    echo "python3 not found, skipping XSD tests"
    exit
fi

python_minor_version=$(python3 --version | cut -d ' ' -f 2 | cut -d '.' -f 2)

if [ $python_minor_version -lt 5 ]; then
    echo "python version less than 3.5, skipping XSD tests"
    exit
fi

if ! command -v javac > /dev/null; then
    echo "javac not found, skipping XSD tests"
    exit
fi

# Java versions are complicated

java_version=$(javac -version | cut -d ' ' -f 2)
javac_major_version=$(echo $java_version | cut -d '.' -f 1)
javac_minor_version=$(echo $java_version | cut -d '.' -f 2)

if [ $javac_major_version -eq 1 ] || [ $javac_minor_version -ge 8 ]; then
    echo "JDK version less than 8, skipping XSD tests"
    exit
fi

python3 check.py ../../src/cbmc/cbmc
