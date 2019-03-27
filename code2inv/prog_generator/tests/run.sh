
filename_list=../../benchmarks/names.txt

while IFS='' read -r line || [[ -n "$line" ]]; do
    echo "$line"
    qsub -v bench=${line},log=logs/${1}/${line}-log  cluster.sub

done < "$filename_list"

