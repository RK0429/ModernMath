-- Quarto extension to display translation links and status

function translation_links()
  -- This is a placeholder for a more advanced implementation
  -- that would read the translation status from the YAML file
  -- and display available translations with their status

  local html = [[
<div class="translation-links">
  <span class="translation-label">Translations:</span>
  <a href="../en/" class="translation-link">🇬🇧 English</a>
  <a href="../ja/" class="translation-link">🇯🇵 日本語</a>
</div>
  ]]

  return pandoc.RawBlock('html', html)
end

-- Register the shortcode
return {
  ['translation-links'] = translation_links
}
