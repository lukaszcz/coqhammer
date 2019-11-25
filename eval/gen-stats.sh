#!/bin/bash

cd tools
make
cd ..
cd atp
../tools/stat , y,p , , false
cd ..
tools/stat -r , y,p , , false

echo "<table>" >> statistics.html
echo "<tr><th>hauto</th><th>hauto 4000</th><th>scrush</th><th></th></tr>" >> statistics.html
echo "<tr>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep 'hauto$' {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep 'hauto 4000' {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep scrush {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep sprover {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep hprover {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "</tr>" >> statistics.html
echo "</table>" >> statistics.html
