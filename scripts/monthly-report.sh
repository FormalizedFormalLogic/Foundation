git log master \
  --since="$(date -d "$(date +%Y-%m-01) -1 month" +%Y-%m-01)" \
  --until="$(date +%Y-%m-01)" \
  --pretty=format:"- \`%h\`: %s" |
sed -E "s/\(#([0-9]+)\)/([#\1](https:\/\/github.com\/FormalizedFormalLogic\/Foundation\/pull\/\1))/"
