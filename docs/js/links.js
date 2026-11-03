// The site's outside links, in one place: the paper, the GitHub repository and the contact address. While one is
// empty, its links show with href "#" (and do nothing), and the build prints a warning.
export const LINKS = { paper: "https://arxiv.org/pdf/2611.02779", github: "https://github.com/GenLang-V/GenDB-V", email: "solidlao.jiale@gmail.com" };

/** The license: the repository's LICENSE once the repository link is set, else the license's own page. */
export function licenseUrl() {
  return LINKS.github ? `${LINKS.github.replace(/\/+$/, "")}/blob/HEAD/LICENSE` : "https://polyformproject.org/licenses/noncommercial/1.0.0";
}

/** Attributes of the link to `kind` (paper, github, email, license); a link not set yet gets href "#" and data-unset. */
export function linkAttrs(kind) {
  const url = kind === "license" ? licenseUrl() : kind === "email" ? (LINKS.email ? `mailto:${LINKS.email}` : "") : LINKS[kind];
  if (!url) return { href: "#", "data-unset": "" };
  return kind === "email" ? { href: url } : { href: url, target: "_blank", rel: "noopener" };
}
