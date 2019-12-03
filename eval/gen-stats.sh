#!/bin/bash

cd tools
make
cd ..
cd atp
../tools/stat , y,p , , false
cd ..
tools/stat -r , y,p , , false

echo "<table>" >> statistics.html
echo "<tr><th>hauto</th><th>hauto 4000</th><th>scrush</th><th>xeauto</th><th>syelles</th></tr>" >> statistics.html
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
echo `find out -name "*.out" -exec grep syelles {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep 'sprover' {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "</tr>" >> statistics.html
echo "</table>" >> statistics.html

echo "<table>" >> statistics.html
echo "<tr><th>rreasy</th><th>rryreconstr</th><th>rrcrush</th><th>rryelles</th><th>rrscrush</th></tr>" >> statistics.html
echo "<tr>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rreasy {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rryreconstr {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rrcrush {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rryelles {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rrscrush {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "</tr>" >> statistics.html
echo "</table>" >> statistics.html

echo "<table>" >> statistics.html
echo "<tr><th>rfirstorder</th><th>rryreconstr</th><th>rrcrush</th><th>rryelles</th><th>rrscrush</th></tr>" >> statistics.html
echo "<tr>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rfirstorder {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rryreconstr {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rrcrush {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rryelles {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "<td>" >> statistics.html
echo `find out -name "*.out" -exec grep rrscrush {} + | wc -l` >> statistics.html
echo "</td>" >> statistics.html
echo "</tr>" >> statistics.html
echo "</table>" >> statistics.html
