for path in "$@"
do
  filename=`basename $path`
  newpath=bench/$filename
  module_name=${filename::-4}
  mkdir -p bench
  sed -r '/^-compile(.*)\.$|^-module(.*)\.$/d' $path > $newpath
  sed -i "1s/^/-module($module_name).\n-export([main\/0]).\n/" $newpath
  sed -ri "s/loop\([1-9][0-9]*,/loop\(1,/" $newpath
  echo -e "\nmain() -> main([]).\n" >> $newpath
done