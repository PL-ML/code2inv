if [ "$#" -ne 2 ]
then
        echo "Usage: $0 path_to_untrained_logs path_to_trained_logs"
        echo "Only for use with logs of the transferability benchmarks"
        echo "eg: $0 logs/logs-fine_tuning-untrained logs/logs-fine_tuning-trained to reproduce the graph in Fig 3b"
        exit
fi

cd plot

for i in $(ls "../$1")
do
        cat "../$1/$i" | tail -10 >> tmp_untrained_stats.txt
done

for i in $(ls "../$2")
do
        cat "../$2/$i" | tail -10 >> tmp_pretrained_stats.txt
done

./get_z3_calls.sh tmp_untrained_stats.txt | sort -n > tmp_untrained.txt
./get_z3_calls.sh tmp_pretrained_stats.txt | sort -n > tmp_pretrained.txt

./plot_learning.py tmp_untrained.txt tmp_pretrained.txt

rm tmp_untrained_stats.txt tmp_pretrained_stats.txt tmp_untrained.txt tmp_pretrained.txt 
cp trained_untrained.pdf ..
