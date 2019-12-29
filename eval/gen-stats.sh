#!/bin/bash

cd tools
make
cd ..
cd atp
../tools/stat , y,p , , false
cd ..
tools/stat -r , y,p , , false

echo "<table>" >> statistics.html
echo "<tr><th>hauto</th><th>xeauto</th><th>scrush</th><th>qcrush</th></tr>" >> statistics.html
echo "<tr>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep 'hauto$' {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep xeauto {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep scrush {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep 'qcrush$' {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "</tr>" >> statistics.html
echo "</table>" >> statistics.html

echo "<table>" >> statistics.html
echo "<tr><th>leauto</th><th>qprover</th><th>syelles</th><th>qcrush2</th></tr>" >> statistics.html
echo "<tr>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep 'leauto' {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep qprover {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep 'syelles' {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep qcrush2 {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "</tr>" >> statistics.html
echo "</table>" >> statistics.html

echo "<table>" >> statistics.html
echo "<tr><th>qblast</th><th>sblast</th><th>sreconstr</th><th>sprover</th></tr>" >> statistics.html
echo "<tr>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep 'qblast' {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep 'sblast' {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep 'sreconstr' {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep sprover {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "</tr>" >> statistics.html
echo "</table>" >> statistics.html

echo "<table>" >> statistics.html
echo "<tr><th>rryelles</th><th>rrcrush</th><th>rryreconstr</th><th>rrblast</th></tr>" >> statistics.html
echo "<tr>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rryelles {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rrcrush {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rryreconstr {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rrblast {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "</tr>" >> statistics.html
echo "</table>" >> statistics.html

echo "<table>" >> statistics.html
echo "<tr><th>rfirstorder</th><th>xeauto</th><th>rtauto</th><th>reasy</th></tr>" >> statistics.html
echo "<tr>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rfirstorder {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep xeauto {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rtauto {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep reasy {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "</tr>" >> statistics.html
echo "</table>" >> statistics.html
