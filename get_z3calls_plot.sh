if [ "$#" -ne 1 ]
then
	echo "Usage: $0 path_to_logs"
	echo "Only for use with logs of the 133 linear C benchmarks"
	echo "eg: $0 logs/logs-c to reproduce the graph in Fig 3a"
	exit
fi

cd plot

for i in $(ls "../$1")
do
	cat "../$1/$i" | head -1 >> tmp_c_stats.csv
done

./get_z3_calls.sh tmp_c_stats.csv | sort -n > tmp_z3calls.txt

./plot_z3calls.py stoch_z3.txt pie_z3.txt ice_z3.txt rl_z3_108.txt tmp_z3calls.txt

rm tmp_c_stats.csv tmp_z3calls.txt
cp z3calls.pdf ..
