exec 2>&1
echo "module agda-nplib where" >$3
git ls-files lib |
  grep '\.agda$' |
  sed -e 's|lib/\(.*\)\.agda|import \1|' |
  tr / . >>$3
