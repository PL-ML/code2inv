filename="$1"

fileno=$(echo $filename | sed -n 's|.*tmp/\(.*\)\.out.*|\1|p')

stats=$(sed -n 's/.* stats: Counter(\(.*\))/\1/p' $filename)

runningtime=$(sed -ne 's/.*z3_report time: \(.*\)pid.*/\1/p' $filename)

iterations=$(sed -ne 's|.*\| \(.*\)/100.*|\1|p' $filename)

totaliter=0
for iter in $iterations
do
    if [ $iter -eq 0 ] || [ $iter -eq 100 ]
    then
        totaliter=$((totaliter+iter))
    else
        totaliter=$((totaliter+iter))
        break
    fi
done

benchname=$(cat ../../../benchmarks/names.txt | head -$(($fileno+1)) | tail -1)

echo $benchname $totaliter $runningtime $stats
