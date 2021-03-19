import csv
import collections

by_class = collections.defaultdict(list)

with open('results.csv') as csvfile:
    reader = csv.reader(csvfile, delimiter=' ', quotechar='|')
    for row in reader:
        clsName, defName, inType, success = row[0], row[1], row[2], row[3]
        by_class[clsName].append(1 if success == "1" else 0)

by_class_avgs = {}
for clsName, results in by_class.items():
    by_class_avgs[clsName] = sum(results) / len(results)

classes = list(by_class.keys())
classes.sort(key=(lambda c: -by_class_avgs[c]))

n_total         = 0
n_success_total = 0

for clsName in classes:
    n   = len(by_class[clsName])
    avg = by_class_avgs[clsName]
    print("%80s %5d %0.2f" % (clsName, n, avg))

    n_total += n
    n_success_total += n * avg

print("----------")
print("Total: (%d / %d) = %0.2f" % (round(n_success_total), n_total, n_success_total / n_total))
