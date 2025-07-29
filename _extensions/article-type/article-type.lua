-- article-type.lua
-- Quarto filter to display article type badge based on YAML front matter

function Meta(meta)
  -- Check if type is defined in metadata
  if meta.type and meta.type.t == "MetaInlines" then
    local article_type = pandoc.utils.stringify(meta.type)

    -- Define type colors and styles
    local type_styles = {
      Definition = {
        bg = "#e3f2fd",
        color = "#1565c0",
        border = "#90caf9"
      },
      Theorem = {
        bg = "#f3e5f5",
        color = "#6a1b9a",
        border = "#ba68c8"
      },
      Example = {
        bg = "#e8f5e9",
        color = "#2e7d32",
        border = "#81c784"
      },
      Axiom = {
        bg = "#fff3e0",
        color = "#e65100",
        border = "#ffb74d"
      },
      Proposition = {
        bg = "#fce4ec",
        color = "#c2185b",
        border = "#f48fb1"
      },
      Lemma = {
        bg = "#f1f8e9",
        color = "#558b2f",
        border = "#aed581"
      },
      Corollary = {
        bg = "#e0f2f1",
        color = "#00695c",
        border = "#4db6ac"
      }
    }

    -- Get style for this type, with default fallback
    local style = type_styles[article_type] or {
      bg = "#f5f5f5",
      color = "#616161",
      border = "#bdbdbd"
    }

    -- Create HTML for the type badge
    local html = string.format([[
<div class="article-type-badge" style="
  display: inline-block;
  padding: 0.25rem 0.75rem;
  margin-bottom: 1rem;
  background-color: %s;
  color: %s;
  border: 1px solid %s;
  border-radius: 0.25rem;
  font-size: 0.875rem;
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.05em;
">%s</div>
]], style.bg, style.color, style.border, article_type)

    -- Store the HTML to be inserted at the beginning of the document
    if not meta._article_type_html then
      meta._article_type_html = pandoc.RawBlock("html", html)
    end
  end

  return meta
end

function Pandoc(doc)
  -- Insert the type badge at the beginning of the document
  if doc.meta._article_type_html then
    table.insert(doc.blocks, 1, doc.meta._article_type_html)
    -- Remove the temporary metadata field
    doc.meta._article_type_html = nil
  end

  return doc
end
