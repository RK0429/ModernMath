-- Translation Metadata Filter for Quarto
-- This filter extracts translation links from YAML front matter and adds them as meta tags

function Meta(meta)
  -- Check if translations field exists
  if meta.translations then
    local translations = meta.translations

    -- Handle translations as a table (the expected format)
    if type(translations) == "table" then
      -- Iterate through each language translation
      for lang, path in pairs(translations) do
        if type(lang) == "string" and type(path) == "string" then
          -- Create meta tag for each translation
          local metaTag = pandoc.RawBlock("html",
            string.format('<meta name="translation-%s" content="%s">', lang, path))

          -- Add to header-includes if it exists, otherwise create it
          if not meta["header-includes"] then
            meta["header-includes"] = pandoc.MetaList({})
          elseif type(meta["header-includes"]) ~= "table" then
            meta["header-includes"] = pandoc.MetaList({meta["header-includes"]})
          end

          table.insert(meta["header-includes"], metaTag)
        end
      end
    end
  end

  return meta
end

return {
  {Meta = Meta}
}
