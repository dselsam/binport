import csv
import collections
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('filename', action='store', type=str)
args = parser.parse_args()

decl2result  = {}
result2count = collections.defaultdict(int)

with open(args.filename) as csvfile:
    reader = csv.reader(csvfile, delimiter=' ', quotechar='|')
    for row in reader:
        if len(row) < 2: continue
        declName, result = row[0], row[1]
        decl2result[declName] = result
        result2count[result] += 1
        print("%120s %s" % (declName, result))

print("----------")
print("Total: (%d / %d) = %0.2f" % (result2count["success"], len(decl2result), result2count["success"] / len(decl2result)))
for result, count in result2count.items():
    print("  %16s: %3d (%0.2f)" % (result, count, count / len(decl2result)))
