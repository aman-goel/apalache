#!/usr/bin/env bash

inputFile="${1}"
shift
apalacheArgs="${1}"
shift
args=$@

shopt -s expand_aliases
source ~/.bash_profile

projectName=$(basename -- "${inputFile}")
projectName="${projectName%.*}"

outPath="runs/${projectName}"

echo -e "--------------------"
echo -e "Project Name: ${projectName}"
echo -e "Input File  : ${inputFile}"
echo -e "Output Path : ${outPath}"

outPath=$(realpath $outPath)

if [ -d "${outPath}" ]; then rm -Rf ${outPath}; fi
mkdir -p ${outPath}
cp ${inputFile} ${outPath}/${projectName}.tla

pushd .
cd ${outPath}
echo -e "--------------------"
echo -e "Compiling TLA+ into VMT with Apalache"
apalache-mc --out-dir=compile transpile ${apalacheArgs} ${projectName}.tla
vmtFile=$(find compile -type f -name "output.vmt")
if [[ -z "$vmtFile" ]]
then
    echo -e "\tNo VMT file found."
    echo -e "Fail"
    exit
fi
echo -e "Success"
popd

pushd .
cd ${GITHUB}/IC3PO
echo -e "--------------------"
echo -e "Running IC3PO"
python3 ic3po.py ${outPath}/${vmtFile} -o ${outPath} -n ${projectName} ${args}
popd
