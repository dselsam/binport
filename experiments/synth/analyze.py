import csv
import collections
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('filename', action='store', type=str)
args = parser.parse_args()

by_class = collections.defaultdict(list)

totals = collections.defaultdict(int)

with open(args.filename) as csvfile:
    reader = csv.reader(csvfile, delimiter=' ', quotechar='|')
    for row in reader:
        if len(row) < 4: continue
        clsName, defName, inType, success = row[0], row[1], row[2], row[3]
        by_class[clsName].append(success)
        totals[success] += 1

by_class_avgs = {}
for clsName, results in by_class.items():
    by_class_avgs[clsName] = sum([1 if result == "success" else 0 for result in results]) / len(results)

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
for status, total in totals.items():
    print("  %16s: %3d (%0.2f)" % (status, total, total / n_total))
