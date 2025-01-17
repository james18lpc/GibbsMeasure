from glob import glob
import os
import re

def pretty_file(filename: str):
    prettyname = filename.replace(".lean", "").replace("/", ".")
    url = f"https://github.com/james18lpc/GibbsMeasure/blob/main/{filename}"
    return f"[{filename}]({url})"

files = [file for tree in os.walk("GibbsMeasure") for file in glob(os.path.join(tree[0], '*.lean'))]
sorries = {}

for file in files:
    with open(file, "r") as f:
        contents = f.read()
    matches = [m.start() for m in re.finditer("sorry", contents)]
    if len(matches) != 0:
        sorries[pretty_file(file)] = len(matches)

result = """
| File | Sorries |
| ---- | ------- |
"""
for file in sorted(sorries.keys()):
    result += f"| {file} | {sorries[file]} |\n"

print(result)
if not os.path.exists("website/_includes"):
    os.makedirs("website/_includes")
with open("website/_includes/sorries.md", "w") as f:
    f.write(result)
